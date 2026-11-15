# Sources and pinned revisions

Access date: 2026-11-15.

## ProveIt / ConciseIPRA

Repository: `VladimirReshetnikov/ProveIt`

Pinned `main` revision inspected:

- `33b0a061e3d8b0a969c8135cf41f94988f2e1ea6`

Files inspected directly:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- directory trees under `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`
- directory listing of `docs/drafts`

Relevant inherited declarations include:

- primitive-recursive symbols `PR` and terms `PTm`;
- axiom family `PRAAx`;
- quantifier-free induction theorem `PRA.qfInd`;
- `native_iff_pra`, `pra_iff_native`, round-trip theorems, and equiconsistency.

The binary draft `docs/drafts/FTA_iPRA.zip` was discovered but not unpacked or audited.

## Mathlib Lindemann analytical part

Repository: `leanprover-community/mathlib4`

Pinned revision used for source location:

- `cbe1882f5b62496bdfc6bbe540a2b3f2db852440`

File:

- `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`

Relevant theorem:

- `LindemannWeierstrass.exp_polynomial_approx`

This is used only as a cross-check for the finite Hermite approximation architecture.

## Conventional Lean proof of pi transcendence

Repository: `gotrevor/lean-formalizations`

Pinned `main` revision inspected:

- `a216ec2d29bbb3f76403a62358e9ca606d0b42f1`

Files inspected:

- `src/LeanFormalizations/NumberTheory/Transcendence/PiTranscendental.lean`
- `.../HermiteLindemann.lean`
- `.../PiLindemann.lean`
- `.../MonicRootSums.lean`
- `.../ETranscendental.lean`

The headline theorem in that repository is:

- `transcendental_pi_axiomClean : Transcendental Q Real.pi`

It is a conventional Lean/Mathlib theorem and is not treated as an iPRA derivation.

## Classical references

- P.-L. Wantzel, 1837, impossibility methods for ruler-and-compass problems.
- F. Lindemann, 1882, transcendence of pi.
- N. Jacobson, *Basic Algebra I*, 2nd ed., Section 4.12, for a modern Hermite-Lindemann presentation.
