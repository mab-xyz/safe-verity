/-
Safe 1.4.1 (`safe-global/safe-smart-account@v1.4.1`), the `execTransaction` core, in Verity.

In scope: `setup` (owners and threshold only), `execTransaction` (four signature kinds, call and
delegatecall, the GS010 gas check, ETH and token refunds), `approveHash`, `receive`, and the getters
that observe them. Storage layout is Safe 1.4.1's, slot for slot. Guard hooks are not implemented:
without `setGuard` the guard slot is always zero, so the original never runs them either.
-/
import Contracts.Common

namespace SafeVerity
open Contracts
open Verity hiding pure bind contractAddress chainid gasPrice
open Verity.EVM.Uint256

/-- `revert(0, 0)`: Solidity's empty revert (SafeMath overflow, ABI decoding, failed
high-level call to an account without code). Executable meaning of the macro's `revertEmpty`. -/
def revertEmpty : Contract Unit := fun s => ContractResult.revert "" s

-- `gasleft()`. Verity has no gas semantics: the Lean model returns 0, so every
-- gas-derived quantity is opaque to proofs (see `README.md`, trust boundary).
verity_intrinsic gasleft (tag : Uint256) : Uint256
  where pure;
        yul := [template (tag) -> g := [ g := gas() ]];
        min_fork := cancun;
        semantics := (fun _ => (0 : Verity.Core.Uint256));
        obligation [gasleft_is_evm_gas := assumed "GAS opcode; the Lean model returns 0"]

def gasleftLowering : Verity.Core.Intrinsics.YulLowering :=
  .template ["tag"] "g" [Compiler.Yul.YulStmt.assign "g" (Compiler.Yul.YulExpr.call "gas" [])]

/-- The Lean model of `gasleft()` at call site `site`: an unknown function. Proofs cannot assume any
value for it, so no theorem holds because of a particular gas amount (the fork's default, a `panic`,
would make every gas check fail in the model and every "on success" theorem vacuous). -/
opaque gasleftModel (site : Uint256) : Uint256

macro_rules
  | `(intrinsic_cancun "gasleft" $_lowering:term [$site:term]) => `(gasleftModel $site)

-- `return(p, size)` from memory. The fork's `returnArray` copies a memory array from calldata,
-- so `getOwners` ABI-encodes its result by hand and returns it with this.
verity_intrinsic memReturn (p : Uint256, size : Uint256) : Uint256
  where pure;
        yul := [template (p, size) -> r := [ yulcall «return»(p, size) ]];
        min_fork := cancun;
        semantics := (fun _ _ => (0 : Verity.Core.Uint256));
        obligation [mem_return_ends_call := assumed "Yul return(p, size); ends the call with that memory slice"]

def memReturnLowering : Verity.Core.Intrinsics.YulLowering :=
  .template ["p", "size"] "r"
    [Compiler.Yul.YulStmt.exprStmt (Compiler.Yul.YulExpr.call "return"
      [Compiler.Yul.YulExpr.ident "p", Compiler.Yul.YulExpr.ident "size"])]

set_option linter.unusedVariables false in
verity_contract Safe where
  storage
    singleton : Address := slot 0
    modules : Address → Uint256 := slot 1
    owners : Address → Uint256 := slot 2
    ownerCount : Uint256 := slot 3
    threshold : Uint256 := slot 4
    nonceSlot : Uint256 := slot 5
    approvedHashesSlot : Address → Uint256 → Uint256 := slot 8

  event_defs
    event ApproveHash(@indexed approvedHash : Bytes32, @indexed owner : Address)
    event ExecutionFailure(@indexed txHash : Bytes32, payment : Uint256)
    event ExecutionSuccess(@indexed txHash : Bytes32, payment : Uint256)
    event SafeReceived(@indexed sender : Address, value : Uint256)

  constants
    sentinel : Uint256 := 1
    -- keccak256("SafeSetup(address,address[],uint256,address,address)")
    safeSetupTopic : Uint256 := 9099209990975222275878227567888657751121033986150727063335030356512757686696
    domainSeparatorTypehash : Uint256 := 32523383700587834770323112271211932718128200013265661849047136999858837557784
    safeTxTypehash : Uint256 := 84814075808141314178395468817534025465894426928601295766380145544921651250904
    -- bytes4(0x20c13b0b) left-aligned
    eip1271Magic : Uint256 := 14815420137760626585476445935662412056931084500740011664602719878907533721600
    -- bytes2(0x1901) left-aligned
    eip712Prefix : Uint256 := 11309588061646438093662687302255421419811724423900836950936401294474059186176
    -- "\x19Ethereum Signed Message:\n32" left-aligned (28 bytes)
    ethSignPrefix : Uint256 := 11430537079145650693387304458692941425836787954612963690241153482819318579200
    addrMask : Uint256 := 1461501637330902918203684832716283019655932542975
    transferSelector : Uint256 := 76450787359836037641860180984291677749980919077056822294353438043884394381312
    maxWord : Uint256 := 115792089237316195423570985008687907853269984665640564039457584007913129639935

  receive := do
    let sender ← msgSender
    let v ← msgValue
    emit "SafeReceived" [sender, v]

  -- Safe 1.4.1 `setup`. Only the owners/threshold part is supported: a module-setup call,
  -- a fallback handler or a setup payment revert with `SV001` (out of scope).
  function setup (_owners : Array Address, _threshold : Uint256, target : Address, data : Bytes,
      fallbackHandler : Address, paymentToken : Address, payment : Uint256,
      paymentReceiver : Address)
    local_obligations [safe_setup_event_encoding := assumed "SafeSetup log data encoded by hand in free memory; tested differentially against solc Safe 1.4.1."]
    : Unit := do
    require (target == zeroAddress && fallbackHandler == zeroAddress && payment == 0)
      "SV001"
    let t ← getStorage threshold
    require (t == 0) "GS200"
    let n := arrayLength _owners
    require (_threshold <= n) "GS201"
    require (_threshold >= 1) "GS202"
    let self ← contractAddress
    let mut current := sentinel
    forEach "i" n (do
      let owner := arrayElement _owners i
      require (owner != zeroAddress && addressToWord owner != sentinel && owner != self
        && addressToWord owner != current) "GS203"
      let existing ← getMapping owners owner
      require (existing == 0) "GS204"
      setMapping owners (wordToAddress current) (addressToWord owner)
      current := addressToWord owner)
    setMapping owners (wordToAddress current) sentinel
    setStorage ownerCount n
    setStorage threshold _threshold
    -- setupModules(address(0), ""): initialises the module list.
    let m ← getMapping modules (wordToAddress sentinel)
    require (m == 0) "GS100"
    setMapping modules (wordToAddress sentinel) sentinel
    -- emit SafeSetup(msg.sender, _owners, _threshold, address(0), address(0)), encoded by hand:
    -- the fork's event encoder mis-addresses calldata array elements.
    let initiator ← msgSender
    let p := mload 64
    unsafe "SafeSetup event data in free memory" do
      mstore p 128
      mstore (add p 32) _threshold
      mstore (add p 64) 0
      mstore (add p 96) 0
      mstore (add p 128) n
    forEach "j" n (do
      unsafe "owner word" do
        mstore (add p (add 160 (mul 32 j))) (addressToWord (arrayElement _owners j)))
    rawLog [safeSetupTopic, addressToWord initiator] p (add 160 (mul 32 n))

  function approveHash (hashToApprove : Bytes32) : Unit := do
    let sender ← msgSender
    let o ← getMapping owners sender
    require (o != 0) "GS030"
    setMappingN approvedHashesSlot [sender, hashToApprove] 1
    emit "ApproveHash" [hashToApprove, sender]

  function view nonce () : Uint256 := do
    let n ← getStorage nonceSlot
    return n

  function view approvedHashes (owner : Address, hash : Bytes32) : Uint256 := do
    let a ← getMappingN approvedHashesSlot [owner, hash]
    return a

  function view getThreshold () : Uint256 := do
    let t ← getStorage threshold
    return t

  function view isOwner (owner : Address) : Bool := do
    let o ← getMapping owners owner
    return (addressToWord owner != sentinel && o != 0)

  function view getChainId () : Uint256 := do
    let c ← chainid
    return c

  function internal view domainSeparatorHash ()
    local_obligations [safe_free_memory_scratch := assumed "Scratch buffer at the free memory pointer; tested differentially against solc Safe 1.4.1."]
    : Bytes32 := do
    let c ← chainid
    let self ← contractAddress
    let p := mload 64
    unsafe "abi.encode(DOMAIN_SEPARATOR_TYPEHASH, chainid, this) in free memory" do
      mstore p domainSeparatorTypehash
      mstore (add p 32) c
      mstore (add p 64) (addressToWord self)
    let h := keccak256 p 96
    return h

  function view domainSeparator ()
    local_obligations [safe_free_memory_scratch := assumed "Scratch buffer at the free memory pointer; tested differentially against solc Safe 1.4.1."]
    : Bytes32 := do
    let ds ← domainSeparatorHash
    return ds


  -- Returns address[] (ABI-encoded by hand, see `memReturn`).
  function getOwners ()
    local_obligations [safe_free_memory_scratch := assumed "Result encoded at the free memory pointer and returned with memReturn; tested against solc Safe 1.4.1."]
    : Uint256 := do
    let count ← getStorage ownerCount
    let p := mload 64
    unsafe "ABI head: offset and length" do
      mstore p 32
      mstore (add p 32) count
    let mut current ← getMapping owners (wordToAddress sentinel)
    forEach "i" count (do
      unsafe "element i" do
        mstore (add p (add 64 (mul 32 i))) current
      current ← getMapping owners (wordToAddress current))
    let done := intrinsic_cancun "memReturn" memReturnLowering [p, add 64 (mul 32 count)]
    return done

  -- Reads the nonce, returns (txHash, safeTxHash) for it, and stores nonce + 1 (Safe: `nonce++`).
  function internal consumeNonce (target : Address, value : Uint256, data : Bytes, operation : Uint8,
      safeTxGas : Uint256, baseGas : Uint256, gasPrice_ : Uint256, gasToken : Address,
      refundReceiver : Address)
    local_obligations [safe_raw_memory_layout := assumed "EIP-712 hashing buffers built in free memory with mstore/calldatacopy; tested differentially against solc Safe 1.4.1."]
    : Tuple [Uint256, Uint256] := do
    let n ← getStorage nonceSlot
    let ds ← domainSeparatorHash
    let p := mload 64
    unsafe "keccak256(data)" do
      copyBytes data p
    let dataHash := keccak256 p (bytesLength data)
    unsafe "abi.encode(SAFE_TX_TYPEHASH, ...)" do
      mstore p safeTxTypehash
      mstore (add p 32) (addressToWord target)
      mstore (add p 64) value
      mstore (add p 96) dataHash
      mstore (add p 128) operation
      mstore (add p 160) safeTxGas
      mstore (add p 192) baseGas
      mstore (add p 224) gasPrice_
      mstore (add p 256) (addressToWord gasToken)
      mstore (add p 288) (addressToWord refundReceiver)
      mstore (add p 320) n
    let safeTxHash := keccak256 p 352
    unsafe "txHashData = abi.encodePacked(0x19, 0x01, domainSeparator, safeTxHash)" do
      mstore p eip712Prefix
      mstore (add p 2) ds
      mstore (add p 34) safeTxHash
    let txHash := keccak256 p 66
    setStorage nonceSlot (add n 1)
    return (txHash, safeTxHash)

  -- Safe 1.4.1 `checkNSignatures(txHash, txHashData, signatures, t)`; `signatures` is execTransaction's
  -- 10th argument (length `sigLen`), read from calldata (head word at 292).
  function internal reentrancy_trusted checkNSignatures (txHash : Uint256, safeTxHash : Uint256,
      sigLen : Uint256, t : Uint256)
    local_obligations [safe_raw_memory_layout := assumed "EIP-1271 call frame built in free memory with mstore/calldatacopy; tested differentially against solc Safe 1.4.1.",
      safe_low_level_calls := assumed "EIP-1271 isValidSignature is a raw staticcall; its result is the adversary model's."]
    : Unit := do
    if t > div maxWord 65 then revertEmpty else pure ()
    let staticPart := mul t 65
    require (sigLen >= staticPart) "GS020"
    let ds ← domainSeparatorHash
    let sigBase := add 36 (calldataload 292)
    let mut lastOwner := 0
    forEach "i" t (do
      let pos := add sigBase (mul 65 i)
      let r := calldataload pos
      let s := calldataload (add pos 32)
      let v := and (calldataload (add pos 33)) 255
      let mut currentOwner := 0
      if v == 0 then
        -- Contract signature (EIP-1271). GS027 holds by construction: txHashData hashes to txHash.
        currentOwner := and r addrMask
        require (s >= staticPart) "GS021"
        if s > sub maxWord 32 then revertEmpty else pure ()
        require (add s 32 <= sigLen) "GS022"
        let csLen := calldataload (add sigBase s)
        if csLen > sub maxWord (add s 32) then revertEmpty else pure ()
        require (add (add s 32) csLen <= sigLen) "GS023"
        if extcodesize currentOwner == 0 then revertEmpty else pure ()
        let q := mload 64
        let padded := mul (div (add csLen 31) 32) 32
        unsafe "abi.encodeWithSelector(isValidSignature(bytes,bytes), txHashData, contractSignature)" do
          mstore q eip1271Magic
          mstore (add q 4) 64
          mstore (add q 36) 192
          mstore (add q 68) 66
          mstore (add q 164) 0
          mstore (add q 100) eip712Prefix
          mstore (add q 102) ds
          mstore (add q 134) safeTxHash
          mstore (add q 196) csLen
          mstore (add q (add 196 padded)) 0
          calldatacopy (add q 228) (add sigBase (add s 32)) csLen
        let ok := staticcall (intrinsic_cancun "gasleft" gasleftLowering [4]) currentOwner q (add 228 padded) 0 0
        if ok == 0 then revertReturndata else pure ()
        if returndataSize < 32 then revertEmpty else pure ()
        unsafe "abi.decode(returndata, (bytes4))" do
          returndataCopy q 0 32
        let magic := and (mload q) (sub 0 (shl 224 1))
        require (magic == eip1271Magic) "GS024"
      else
        if v == 1 then
          -- Approved hash: the approver is r; msg.sender approves implicitly.
          currentOwner := and r addrMask
          let sender ← msgSender
          let approved ← getMappingN approvedHashesSlot [wordToAddress currentOwner, txHash]
          require (addressToWord sender == currentOwner || approved != 0) "GS025"
        else
          if v > 30 then
            let q := mload 64
            unsafe "keccak256(abi.encodePacked(\"\\x19Ethereum Signed Message:\\n32\", txHash))" do
              mstore q ethSignPrefix
              mstore (add q 28) txHash
            let prefixed := keccak256 q 60
            let signer ← ecrecover prefixed (sub v 4) r s
            currentOwner := addressToWord signer
          else
            let signer ← ecrecover txHash v r s
            currentOwner := addressToWord signer
      let isOwnerWord ← getMapping owners (wordToAddress currentOwner)
      require (currentOwner > lastOwner && isOwnerWord != 0 && currentOwner != sentinel) "GS026"
      lastOwner := currentOwner)

  -- GS013: with neither safeTxGas nor gasPrice, the inner call must succeed.
  function internal requireOutcome (success : Uint256, safeTxGas : Uint256, gasPrice_ : Uint256) : Unit := do
    require (success == 1 || safeTxGas != 0 || gasPrice_ != 0) "GS013"

  -- handlePayment's amount: (gasUsed + baseGas) * price, price = min(gasPrice, tx.gasprice) for ETH and
  -- gasPrice for a token; SafeMath overflow reverts empty.
  function internal paymentAmount (gasUsed : Uint256, baseGas : Uint256, gasPrice_ : Uint256,
      gasToken : Address, txPrice : Uint256) : Uint256 := do
    if gasUsed > sub maxWord baseGas then revertEmpty else pure ()
    let base := add gasUsed baseGas
    let price := if gasToken == zeroAddress then min gasPrice_ txPrice else gasPrice_
    if base != 0 && price > div maxWord base then revertEmpty else pure ()
    return (mul base price)

  -- Safe 1.4.1 `execTransaction`, without guard hooks (no guard can be set).
  function payable reentrancy_trusted execTransaction (target : Address, value : Uint256,
      data : Bytes, operation : Uint8, safeTxGas : Uint256, baseGas : Uint256,
      gasPrice_ : Uint256, gasToken : Address, refundReceiver : Address, signatures : Bytes)
    local_obligations [safe_raw_memory_layout := assumed "Call frames built in free memory with mstore/calldatacopy; tested differentially against solc Safe 1.4.1.",
      safe_low_level_calls := assumed "call/delegatecall execution, ETH send and token transfer are raw calls; their effects are the adversary model's."]
    : Bool := do
    -- Enum.Operation ABI decoding: values other than 0 and 1 revert.
    if operation > 1 then revertEmpty else pure ()
    let (txHash, safeTxHash) ← consumeNonce target value data operation safeTxGas baseGas gasPrice_ gasToken refundReceiver
    -- checkSignatures(txHash, txHashData, signatures)
    let t ← getStorage threshold
    require (t > 0) "GS001"
    checkNSignatures txHash safeTxHash (bytesLength signatures) t
    -- 1/64 rule and event headroom, Solidity 0.7 wrapping arithmetic.
    let g0 := intrinsic_cancun "gasleft" gasleftLowering [1]
    require (g0 >= add (max (div (mul safeTxGas 64) 63) (add safeTxGas 2500)) 500) "GS010"
    let gasStart := intrinsic_cancun "gasleft" gasleftLowering [2]
    let txGas := if gasPrice_ == 0 then sub (intrinsic_cancun "gasleft" gasleftLowering [3]) 2500 else safeTxGas
    let d := mload 64
    unsafe "execute: data to memory" do
      copyBytes data d
    let mut success := 0
    if operation == 1 then
      success := delegatecall txGas (addressToWord target) d (bytesLength data) 0 0
    else
      success := call txGas (addressToWord target) value d (bytesLength data) 0 0
    let gasEnd := intrinsic_cancun "gasleft" gasleftLowering [5]
    if gasEnd > gasStart then revertEmpty else pure ()
    let gasUsed := sub gasStart gasEnd
    requireOutcome success safeTxGas gasPrice_
    let mut payment := 0
    if gasPrice_ > 0 then
      let txSender ← txOrigin
      let receiver := if refundReceiver == zeroAddress then addressToWord txSender else addressToWord refundReceiver
      let txPrice ← gasPrice
      payment ← paymentAmount gasUsed baseGas gasPrice_ gasToken txPrice
      if gasToken == zeroAddress then
        let sent := call (mul (if payment == 0 then 1 else 0) 2300) receiver payment 0 0 0 0
        require (sent == 1) "GS011"
      else
        let q := mload 64
        unsafe "abi.encodeWithSelector(0xa9059cbb, receiver, payment)" do
          mstore q transferSelector
          mstore (add q 4) receiver
          mstore (add q 36) payment
        let ok := call (sub (intrinsic_cancun "gasleft" gasleftLowering [6]) 10000) (addressToWord gasToken) 0 q 68 q 32
        let rds := returndataSize
        let word := mload q
        let transferred := if rds == 0 then ok else (if rds == 32 then (if ok == 1 && word != 0 then 1 else 0) else 0)
        require (transferred == 1) "GS012"
    else
      pure ()
    if success == 1 then
      emit "ExecutionSuccess" [txHash, payment]
    else
      emit "ExecutionFailure" [txHash, payment]
    return (success == 1)

end SafeVerity
