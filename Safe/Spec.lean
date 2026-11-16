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

end SafeVerity.Spec
