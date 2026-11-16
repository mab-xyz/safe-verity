import Safe.Contract

/-!
# Specification vocabulary

What the Safe signs and checks, stated independently of how the contract lays bytes out in memory.
-/

namespace SafeVerity.Spec
open Verity Contracts

/-- `keccak256(abi.encode(w₀, …, wₖ))` truncated to `size` bytes: Keccak-256 of the 32-byte
big-endian words, concatenated (`abi.encode` of static words is exactly this concatenation). -/
def keccakWords (ws : List Nat) (size : Nat) : Uint256 :=
  Verity.Core.Uint256.ofNat
    (KeccakEngine.byteArrayToNatBE
      (KeccakEngine.keccak256
        ((ws.foldl (fun acc w => acc ++ Compiler.Keccak.MemorySlice.wordToBytesBE w) ByteArray.empty).extract 0 size)))

/-- EIP-712 domain separator: `keccak256(abi.encode(DOMAIN_SEPARATOR_TYPEHASH, chainId, this))`. -/
def domainSeparator (chainId : Uint256) (self : Address) : Uint256 :=
  keccakWords [Safe.domainSeparatorTypehash.val, chainId.val, (addressToWord self).val] 96

/-- `keccak256(abi.encode(SAFE_TX_TYPEHASH, to, value, keccak256(data), operation, safeTxGas,
baseGas, gasPrice, gasToken, refundReceiver, nonce))`. -/
def safeTxHash (target : Address) (value dataHash operation safeTxGas baseGas gasPrice : Uint256)
    (gasToken refundReceiver : Address) (nonce : Uint256) : Uint256 :=
  keccakWords [Safe.safeTxTypehash.val, (addressToWord target).val, value.val, dataHash.val,
    operation.val, safeTxGas.val, baseGas.val, gasPrice.val, (addressToWord gasToken).val,
    (addressToWord refundReceiver).val, nonce.val] 352

/-- `keccak256(0x19 ‖ 0x01 ‖ domainSeparator ‖ safeTxHash)` (66 bytes), as three words. -/
def txHash (ds sth : Uint256) : Uint256 :=
  keccakWords [(Verity.EVM.Uint256.or Safe.eip712Prefix (Verity.EVM.Uint256.shr 16 ds)).val,
    (Verity.EVM.Uint256.or (Verity.EVM.Uint256.shl 240 ds) (Verity.EVM.Uint256.shr 16 sth)).val,
    (Verity.EVM.Uint256.shl 240 sth).val] 66

/-! ## Signatures, as `execTransaction`'s calldata carries them -/

/-- The 32-byte calldata word at byte offset `o` (what `calldataload(o)` returns). -/
def cdWord (s : ContractState) (o : Uint256) : Uint256 :=
  Verity.Core.Uint256.ofNat (Compiler.CompilationModel.Denote.calldataloadWord s.selector s.calldata o.val)

/-- Calldata offset of the first signature byte: `signatures` is `execTransaction`'s 10th
argument, whose ABI head word sits at byte 292. -/
def sigBase (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.add 36 (cdWord s 292)

/-- Signature `i` is the 65 bytes `r ‖ s ‖ v` at `sigBase + 65 i`. -/
def sigPos (s : ContractState) (i : Uint256) : Uint256 :=
  Verity.EVM.Uint256.add (sigBase s) (Verity.EVM.Uint256.mul 65 i)
def sigR (s : ContractState) (i : Uint256) : Uint256 := cdWord s (sigPos s i)
def sigS (s : ContractState) (i : Uint256) : Uint256 := cdWord s (Verity.EVM.Uint256.add (sigPos s i) 32)
def sigV (s : ContractState) (i : Uint256) : Uint256 :=
  Verity.EVM.Uint256.and (cdWord s (Verity.EVM.Uint256.add (sigPos s i) 33)) 255

/-- What the contract's `ecrecover` returns for `(hash, v, r, s)` (the precompile, an oracle). -/
def recover (h v r sg : Uint256) : Uint256 :=
  match Contracts.ecrecover h v r sg Verity.defaultState with
  | .success a _ => addressToWord a
  | .revert _ _ => 0

/-- `keccak256("\x19Ethereum Signed Message:\n32" ‖ hash)`, the eth_sign digest (60 bytes). -/
def ethSignHash (h : Uint256) : Uint256 :=
  keccakWords [(Verity.EVM.Uint256.or Safe.ethSignPrefix (Verity.EVM.Uint256.shr 224 h)).val,
    (Verity.EVM.Uint256.shl 32 h).val] 60

/-- `owners[o]` in state `s` (non-zero iff `o` is in the owner list or is the sentinel). -/
def ownerLink (s : ContractState) (o : Uint256) : Uint256 :=
  s.storageWords (.map Safe.owners.slot (wordToAddress o))

/-- `approvedHashes[o][h]` in state `s`. -/
def approved (s : ContractState) (o h : Uint256) : Uint256 :=
  s.storageWords (.mapChain Safe.approvedHashesSlot.slot
    [Contracts.StorageKey.toWord (wordToAddress o), Contracts.StorageKey.toWord h] 0)

/-- How signature `i` authorises signer `o` for `txHash`, per signature kind `v`. For a contract
signature (`v = 0`) only the claimed signer is pinned down here; its `isValidSignature` answer is a
raw call result, tested but not modelled (see README, trust boundary). -/
def Authorizes (s : ContractState) (txHash : Uint256) (i : Uint256) (o : Uint256) : Prop :=
  let v := sigV s i
  let r := sigR s i
  (v = 0 ∧ o = Verity.EVM.Uint256.and r Safe.addrMask) ∨
  (v = 1 ∧ o = Verity.EVM.Uint256.and r Safe.addrMask ∧
    (addressToWord s.sender = o ∨ approved s o txHash ≠ 0)) ∨
  (v > 30 ∧ o = recover (ethSignHash txHash) (Verity.EVM.Uint256.sub v 4) r (sigS s i)) ∨
  (v ≠ 0 ∧ v ≠ 1 ∧ ¬ v > 30 ∧ o = recover txHash v r (sigS s i))

end SafeVerity.Spec
