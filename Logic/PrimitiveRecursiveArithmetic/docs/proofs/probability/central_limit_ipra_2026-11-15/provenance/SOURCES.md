# Sources and inspected repository state

## Requested reference pages

- Wikipedia, **Central limit theorem**, accessed 2026-11-15: <https://en.wikipedia.org/wiki/Central_limit_theorem>
- Wolfram MathWorld, **Central Limit Theorem**, page marked updated 2026-11-14 and accessed 2026-11-15: <https://mathworld.wolfram.com/CentralLimitTheorem.html>

The manuscript treats these as a statement inventory, not as proof authorities. It explicitly corrects two overbroad MathWorld phrasings: finite variances alone do not imply a CLT for an arbitrary non-identical array, and a general sample average is asymptotically rather than exactly Gaussian.

## ProveIt

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Revision inspected for this packet:

- commit `979613af639a0e33b9d17b74af2a5629bb2d749f`
- main-branch commit time `2026-11-15T23:46:56Z`
- `lean-toolchain`: `leanprover/lean4:v4.32.0`

Relevant paths:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/calculus_ipra`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/stirling_ipra`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/taylor_cauchy_ipra`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/bohr_mollerup_ipra_2026-11-15`

The packet follows their regular-interval-name convention and their distinction between a semantic Lean proof and an actual `PRAAx` derivation. The existing theorem `pra_iff_native` is the intended final bridge to ConciseIPRA's native scalar calculus.

## Classical proof ingredients

The proof is self-contained at the mathematical level. Standard historical labels are used for:

- Esseen's smoothing inequality;
- the Berry--Esseen theorem;
- the Lindeberg and Lyapunov conditions;
- Robbins' explicit Stirling bounds;
- de Moivre--Laplace;
- Cramer--Wold;
- the lattice Fourier inversion formula.

A modern comparison source for the Fourier strategy is Roman Vershynin,
*Two Friendly Proofs of the Berry--Esseen Theorem*, arXiv:2602.06234 (first
version February 2026; expanded version July 2026). The exact constants in
this packet are independently re-derived and deliberately non-optimal.
