# ProveIt source inspection for the isoperimetric packet

Inspected using the GitHub connector at commit `329161f8da0b319d51ba9f6246c4b19d243f7193`.
The commit timestamp is `2026-11-15T04:58:40Z` (14 November in the user's Pacific timezone).
These are read-only observations, not a claim to have rebuilt the repository.

## Toolchain and dependency

- Root `lean-toolchain`: `leanprover/lean4:v4.32.0`.
- Root `lake-manifest.json`: Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`, input revision `v4.32.0`.
- Root `lakefile.toml` declares library `ConciseIPRA` with source directory
  `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.
- Common local executable paths and PATH contained no Lean or Lake compiler.
  The proposed new code therefore must be labelled uncompiled in this environment.

## Actual arithmetic target

`ConciseIPRA.PR` imports `ConciseIPRA.Deduction`. Its namespace is
`LeanProofs.ConciseIPRA`. It defines:

1. `PR : Nat -> Type`, function symbols by zero, successor, projections,
   composition and primitive recursion.
2. `PTm n`, arithmetic terms in `n` free variables.
3. `PRAAx : Theory PTm`, defining equations, the successor axioms, and
   induction **only for quantifier-free formulas**.
4. `PRA.qfInd`, the derived internal rule of quantifier-free induction.

`ConciseIPRA.Syntax` defines first-order formulas `Fm T n` with equality,
bottom, conjunction, disjunction, implication, universal and existential
quantification. `Fm.QF` excludes both quantifiers. Binder index zero is the
new variable. `ConciseIPRA.Deduction` defines the intuitionistic derivability
judgment `Prf Ax Gamma phi`, with notation `Gamma ⊢[Ax] phi`. Its constructors
are the ordinary intuitionistic natural-deduction rules, substitution of
open axioms, reflexivity and simultaneous equality transport.

Consequently the correct completed endpoint for this project is an inhabitant
of `Prf PRAAx [] isoperimetricFormula`, where the finite arithmetic formula has
been explicitly constructed. An ordinary Lean theorem about rational numbers,
real numbers, or polygons is useful intermediate work but is not this endpoint.
Absence of `Classical.choice` in such a theorem is not enough to establish
provability in iPRA.

## Existing transfer theorems

`ConciseIPRA.BiInterpretation` provides `biInterp : BiInterp TeqAx PRAAx`,
`teq_iff_pra`, `pra_iff_teq`, `teq_theorem_iff`, `pra_theorem_iff`, and both
round trips. `ConciseIPRA.NativeBiInterpretation` provides `NFm.toPRA`,
`NFm.ofPRA`, `native_iff_pra`, `pra_iff_native` and both native round trips.
Thus the most direct path is to prove the arithmetic statement in the ordinary
iPRA embedding and transfer it afterwards if the concise native presentation
is wanted.

The README reports that its existing modules build without `sorry` or warnings.
It says the final results use only the Lean axioms `propext`, `Classical.choice`
and `Quot.sound`, with the ordinary T_eq/iPRA equivalence using only `propext`
and `Quot.sound`. This is a report about the repository's metatheory; it does
not insert excluded middle into the embedded iPRA object logic. No rebuild
or independent axiom audit was performed here.

## Reuse decision

Use `ConciseIPRA.PR`, `ConciseIPRA.Deduction`, and optionally the transfer
theorems. Do not make a geometric proof depend on the much larger Busy Beaver
or Diophantine consistency projects merely because those were permitted.
A repository code search for `isoperimetric` returned no hits. The inspected
`Analysis/TrigonometricIdentities/Lean/TrigonometricIdentities.lean` imports
`ArctanSquareIdentity` and `TrigGoldenRatio`; no directly relevant internal
iPRA isoperimetric lemma was identified. This is not an exhaustive proof of
absence across every repository file.

## Representation caveat for the curve corollary

Primitive recursive programs have no primitive-recursive universal evaluator.
Do not quantify over arbitrary PR program codes and silently evaluate all of
them with one PR function. The rational polygon theorem can be a single
universal arithmetic statement over finite codes. The curve corollary should
be a schema for fixed primitive-recursive approximation and modulus symbols,
or should include explicitly bounded computation traces and an explicit
primitive-recursive bound. All loop invariants used internally must be encoded
as finite rational identities or Boolean bounded conjunctions before applying
`PRA.qfInd`.

## Pinned sources

- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/lean-toolchain
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/lake-manifest.json
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/lakefile.toml
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/329161f8da0b319d51ba9f6246c4b19d243f7193/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean
