# safe-verity

The core of [Safe](https://github.com/safe-global/safe-smart-account) 1.4.1, `execTransaction`, written in
[Verity](https://github.com/mab-xyz/verity) (a Lean 4 language for smart contracts) and compiled by Verity to EVM
bytecode. Lean proves four properties of the contract. Foundry runs one test suite, unchanged, against the
Verity bytecode and against the original Safe 1.4.1, and requires the same results from both.

## What is implemented

`Safe/Contract.lean`, with Safe 1.4.1's storage layout slot for slot:

- `execTransaction(to, value, data, operation, safeTxGas, baseGas, gasPrice, gasToken, refundReceiver, signatures)`
  (selector `0x6a761202`):
  - the EIP-712 `safeTxHash` over the current nonce, then `nonce++`;
  - all four signature kinds: ECDSA, `eth_sign` (`v > 30`), approved hash or `msg.sender` (`v = 1`), and EIP-1271
    contract signatures (`v = 0`);
  - the GS0xx checks: strictly increasing owners, length and pointer bounds;
  - call and delegatecall, and the GS010 gas check and GS013 rule;
  - ETH and ERC-20 gas refunds, the `ExecutionSuccess` and `ExecutionFailure` events, and every revert string and
    empty revert of the original.
- `setup` with the 1.4.1 signature. Only the owners and threshold are supported: a non-zero `to`,
  `fallbackHandler` or `payment` reverts with `SV001`.
- `approveHash`, `receive`, and the getters `nonce`, `getThreshold`, `getOwners`, `isOwner`, `approvedHashes`,
  `domainSeparator` and `getChainId`.

It is a standalone contract: it does not need `SafeProxy`, and it can also serve as a proxy's singleton.

Not implemented:
- guard hooks (nothing can set a guard, so the original never runs them either);
- modules, the fallback handler, and owner management (`addOwnerWithThreshold`, …);
- the public getters `checkSignatures`, `getTransactionHash`, `encodeTransactionData`, `signedMessages` and
  `VERSION`.

Two differences from the original that callers can see:
- `getOwners` is declared `uint256[]` and non-`view` in the ABI JSON. The bytes on the wire are the same as
  `address[]`. The reasons are fork bugs, listed below.
- Gas use differs from the solc build.

## Reproduce

```
lake build                      # contract, spec and proofs (Lean 4.31, the fork's toolchain)
scripts/build.sh                # Verity → Yul → out/Safe.bin (needs solc ≥ 0.8.26)
forge test                      # 61 behaviour tests × 2 builds + 3 differential fuzzers × 512 runs
python3 scripts/mutate.py       # 21 mutants of the Verity source; prints only the survivors, exit 0 if none
```

`lake build` checks every theorem. `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`
for each one: there is no `sorry` and no project axiom.

## The properties

They are stated about the Verity model of the contract (`Safe.*_registry`). That model reads live calldata and
runs external calls through Verity's adversary model.

**P1, signatures** (`Safe/Proofs/Signatures.lean`, `checkNSignatures_sound`). If `checkNSignatures(txHash, …, t)`
succeeds, it found `t` signers `o₀ < … < oₜ₋₁` (so pairwise distinct). Each is not the sentinel
`0x1`, each has `owners[o] ≠ 0`, and each authorises `txHash` as its signature's `v` byte selects
(`Spec.Authorizes`):
- ECDSA: `o = ecrecover(txHash, v, r, s)`;
- `eth_sign`: `o = ecrecover(keccak("\x19Ethereum Signed Message:\n32" ‖ txHash), v − 4, r, s)`;
- approved hash: `o = r`, and `msg.sender = o` or `approvedHashes[o][txHash] ≠ 0`;
- contract signature: `o = r` (the `isValidSignature` answer is not covered; see the trust boundary).

The signatures are the bytes at `sigBase + 65i` of the transaction's calldata. Storage, calldata, the caller and
the contract address are unchanged by the check. *Attack ruled out:* executing with fewer than `threshold`
distinct owners, or one owner counted twice.

**P2, nonce** (`Safe/Proofs/Nonce.lean`, `consumeNonce_spec`). `consumeNonce` always succeeds. It returns
`txHash = keccak(0x19 ‖ 0x01 ‖ domainSeparator(chainId, this) ‖ safeTxHash)`, where `safeTxHash` is the Keccak of
the 11 ABI words `(SAFE_TX_TYPEHASH, to, value, keccak(data), operation, safeTxGas, baseGas, gasPrice, gasToken,
refundReceiver, n)` and `n` is the nonce in storage. Its only storage effect is `nonce := n + 1`. *Attack ruled
out:* replay. A set of signatures is valid for one nonce, and that nonce is consumed before any external call.

**P1 ∘ P2** (`Safe/Proofs/ExecTransaction.lean`, `execTransaction_authorized`). If `execTransaction` succeeds
from state `s`, then `threshold(s)` distinct owners of `s` authorised the EIP-712 hash of exactly these
parameters, at the nonce of `s`.

**P3, frame** (`Safe/Proofs/Storage.lean`, `execTransaction_writes_only_nonce`). Assume no external call changes
the Safe's storage (`StorageInert`). Then a successful `execTransaction` ends with the storage it started with,
except `nonce := nonce + 1`. Owners, threshold and modules can therefore change only through the signed inner
call, for example a delegatecall or a call to the Safe itself.

**P4, outcome and refund** (`Safe/Proofs/Payment.lean`):
- `requireOutcome_success_iff`: the post-call check passes iff the inner call succeeded, or `safeTxGas ≠ 0`, or
  `gasPrice ≠ 0` (GS013).
- `paymentAmount_eq`: the refund is SafeMath's `(gasUsed + baseGas) × price`, with an empty revert on overflow.
  `price` is `min(gasPrice, tx.gasprice)` for ETH and `gasPrice` for a token.

Verity has no gas semantics, so `gasUsed` is an arbitrary input. `execTransaction` calls both helpers, but there
is no end-to-end theorem from its return value back to GS013.

## Testing the bytecode

- **Reference:** `lib/safe-smart-account` at tag `v1.4.1`, compiled with solc 0.7.6 as released, deployed behind
  its `SafeProxy`.
- **`test/SafeBehaviour.t.sol`:** 61 scenarios, run on both builds:
  - setup checks and storage layout;
  - every signature kind and every GS020–GS026 rejection, including the `address(1)` sentinel;
  - EIP-1271 pointer bounds, bubbled reverts, short and dirty return data;
  - call and delegatecall, GS010 and GS013, ETH and token refunds (four token return shapes), events.
- **`test/SafeDifferential.t.sol`:** both builds side by side under fuzzing. They must agree bit for bit on the
  success flag, the return or revert data, the nonce, and the effects on the target and the Safe. Inputs: signer
  subsets, mixed signature kinds, corrupted bytes, value, data, delegatecall, reverting targets, garbage signature
  blobs, and fuzzed `setup` arguments.
- **`scripts/mutate.py`:** 21 mutants, all killed. Each breaks one security-relevant line: the nonce increment or
  hash, owner ordering, the sentinel and owner checks, a signature-kind branch, a bounds check, the EIP-1271 magic
  value, GS010, GS013, the refund price or receiver, or a setup or `approveHash` guard.

## Trust boundary

What the theorems assume, or do not see:

- **The compiler.** The Verity fork compiles the model to Yul. Its EDSL→Yul preservation theorem does not cover
  loops with bodies, raw memory or raw calls, and this contract uses all three. The link between the theorems and
  the bytecode is therefore the test suite, not a proof.
- **Raw mechanics, declared as `local_obligations`.** Hash pre-images and call frames are built with
  `mstore`/`calldatacopy` in free memory. The calls themselves are raw: `call`, `delegatecall`, the EIP-1271
  `staticcall`, the ETH `send`, the token `transfer`, and `return` from memory in `getOwners`.
- **Gas.** `gasleft()` is the opaque `gasleftModel`, so no theorem depends on a gas value.
- **`ecrecover`.** The model calls it as an oracle. In the fork today that oracle defaults to the sum of its
  arguments, which is forgeable (fork bug). P1 never uses its definition, so P1 holds for the real precompile
  exactly when the precompile is ECDSA recovery.
- **EIP-1271.** For `v = 0`, P1 proves that the signer is the owner contract named in `r`, but not that it
  approved. Two fork gaps prevent more: the EDSL's `revertReturndata` does not revert, and the call frame is
  unaligned in a word-keyed memory model. The approval itself is tested on both builds.
- **`keccak(data)`.** P2 takes `keccak(data)` as given. That the model hashes `data` correctly is a property of
  `copyBytes`/`keccak256Live`, which the fork does not prove.
- **P3's hypothesis.** `StorageInert` excludes reentry into the Safe and delegatecall effects.

## Fork bugs found

Each one has a plan in `~/verity`, and has a minimal reproduction in `Repro/` where one exists.

- `plan-event-array-param-encoding.md`: events with an `Array` parameter read every element one word off, and
  fail to compile with solc.
- `plan-revert-empty-executable.md`: the macro accepts `revertEmpty`, but no Lean definition exists for it.
- `plan-view-frame-theorem-loops.md`: a parameterless `view` function with a state-threading `forEach` fails to
  elaborate.
- `plan-nullary-builtin-intrinsic.md`: a zero-input builtin such as `gas()` cannot be declared as an intrinsic.
- `plan-docs-foreach-mutable-locals.md`: the docs say `let mut` inside `forEach` is rejected. It works.
- `plan-intrinsic-wrapper-call-miscompile.md`: an intrinsic called by its wrapper name compiles to its Lean
  semantics, here `gasleft() → 0`, a silent miscompilation. Its explicit form has a `panic` model meaning, which
  makes "on success" theorems vacuous.
- `plan-return-memory-array.md`: `returnArray` of a memory array copies from calldata.
- `plan-ite-expression-evaluates-both-branches.md`: in the compiled code, an `if`-expression evaluates the branch
  not taken, which may revert.
- `plan-edsl-byte-addressed-memory.md`: model memory is word-keyed, so unaligned `mstore`/`keccak` hash other
  bytes than the EVM does.
- `plan-ecrecover-oracle.md`, from another project, with this one as a second witness: in the EDSL, `ecrecover`
  is the sum of its arguments.
- `plan-revert-returndata-reverts-in-edsl.md`: in the EDSL, `revertReturndata` is a no-op.

## Layout

```
Safe/Contract.lean        the contract (verity_contract Safe)
Safe/Spec.lean            hashes, signature layout, Authorizes
Safe/Proofs/*.lean        Frame (frames, loop chains), Nonce (P2), Signatures (P1),
                          ExecTransaction (P1∘P2), Storage (P3), Payment (P4)
SafeCompile.lean          lake exe safe-compile OUT → Yul + ABI
test/                     Foundry suites; test/ref/SafeRef.sol pulls in the original Safe 1.4.1
Repro/                    minimal reproductions of fork bugs (lake exe repro-compile)
```

## License

MIT for this repository's code. Safe 1.4.1 (in `lib/`, used only as the test reference) is LGPL-3.0.
