# Additive arithmetic in conventional HA: author receipt

Author: `circuit_reduction`. This records author review and fresh leaf builds,
not an independent peer review. Both complete new sources and both private
drivers were read before execution; the final sources were reread at freeze.
No frozen source, shared object, umbrella, vendor file or Git state was edited.

## Frozen files and build provenance

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/HAAdditiveArithmetic.lean` | 111 | `5f1f38a64058607e9e6ac499d8706487ed70ec8c505d19a797b40af242ecaae6` |
| `Lean/DiophantineConsistency/HAAdditiveArithmeticChecks.lean` | 81 | `6709af679585c2be46f299aec8f7c8d186fda586a889d67f15c17412a69ee0e5` |
| `reviews/ha-additive-arithmetic-dependency-replay.json` | — | `bc5aaf438b0cef83e089b02a87e09c8465829d75954d1f633c1273944b78d0a9` |

The selected closure was authenticated against unchanged source bytes,
compiler, toolchain and package manifest at snapshot
`f1835fa65074d6f320dc169e3b52e86052c70a09`. Eight custom prerequisites were
reused: the five PAHF closure modules, `HAProofs`, `HADeduction`, and the frozen
`HABasicArithmetic` main. No prerequisite was freshly rebuilt. The new main
imports only `HABasicArithmetic`; neither Foundation nor the native-equation
closure is imported by this packet.

The frozen Basic main/check sources, objects, logs, manifest and all 19 prior
axiom audits were explicitly reauthenticated and remain unchanged. They were
not replayed as part of this new leaf build. The JSON receipt gives every
selected source/object hash, reused object location, exact fresh command,
terminal exit code, log hash and private driver hash.

Both new leaves passed their first sequential direct fresh builds with
`-M6000 -j1` and source-level `Elab.async false`, in private overlay
`/tmp/ha-additive-arithmetic-_r5n0ugs`. Both terminal exit codes were zero.
The main log is empty; the checks log contains exactly 14 axiom reports, each
using only `propext` and/or `Quot.sound`. There are no final warnings,
`sorry`, `native_decide`, custom axioms, `Classical.choice`, model arguments
or classical PA proof conversions in the new results.

Fresh main object:
`10b8cb4af6b47f595ccd008cfb5e8740342a1e697c712572508f985dc01f5e41`.
Fresh checks object:
`42c75f6ee4aff5a6857b43703e1af04baf0d8337ba75992ddf8757a39819eb66`.

## Exact proof content

The six public theorems are in `DiophantineConsistency.HA.Arithmetic`:
`succ_add_all`, `succ_add`, `add_comm_all`, `add_comm`, `add_assoc_all`, and
`add_assoc`. Each `_all` theorem proves an actual universally quantified
formula in `HA.Proves`, using the already checked `Arithmetic.induction`
rule for a concrete formula. This applies the conventional sealed
`Formula.Ax_s_induction` schema; it is not metatheoretic induction on a
standard natural number standing in for the object variable.

The induction variable is index zero. Each arbitrary ambient term is
renamed by `Nat.succ` before entering the formula. Zero substitution removes
that slot and restores the ambient terms; successor substitution changes
only index zero and preserves the shifted parameters. The step proofs use
the actual induction hypothesis in a finite relative context, arithmetic
axiom instances weakened into that context, and HA equality congruence and
transitivity. Universal introduction uses the explicit sentence property
of `Formula.Ax_s`. The arbitrary-term results then instantiate the proved
universal formula using the actual HA elimination rule.

Successor addition is proved first from right-successor addition, then used
with `zero_add` for commutativity. Associativity uses right-successor
addition and the induction hypothesis under successor. Existing classical
`PASyntax` proofs were inspected only as binder-bookkeeping guides; none is
called. Only their independent syntax-substitution identities are reused.

## Focused checks and remaining scope

Checks prove exact generic zero/successor substitution identities for the
two-parameter associativity body. They also prove a two-quantifier HA
associativity theorem with a genuine free parameter, reopen both binders
with arbitrary terms, and retain parameter zero even when those terms use
it. Further checks instantiate all three arithmetic results with nonlinear
terms containing several distinct free indices, compose commutativity with
associativity in HA, and exercise literal zero/successor cases.

This packet supplies conventional HA additive identities. It does not yet
prove the remaining multiplication/order axioms, full arithmetic-theory
transport from Foundation, or the final HA consistency-equivalence theorem.
