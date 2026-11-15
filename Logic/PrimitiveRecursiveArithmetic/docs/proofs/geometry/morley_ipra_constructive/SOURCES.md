# Sources and revision pins

## Morley's theorem and proof lineage

- Wikipedia, “Morley's trisector theorem,” accessed 15 November 2026:
  <https://en.wikipedia.org/wiki/Morley%27s_trisector_theorem>
- B. Bollobás, *The Art of Mathematics: Coffee Time in Memphis*, Cambridge
  University Press, 2006, pp. 126-127.  The human proof uses this short
  trigonometric factorization as its readable starting point.
- B. Puyobro, “Morley's Theorem,” Archive of Formal Proofs, 7 March 2025:
  <https://isa-afp.org/entries/Morley_Theorem.html>
- Solarys431, `UnicoProofs/Morley.lean`, repository revision
  `794568d279e377c34e3ab93a5e0626467f7d9e0d`:
  <https://github.com/Solarys431/unico-lean-proofs>

## ProveIt / iPRA infrastructure

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>
- Inspected revision: `0bba41d70f061442357cae0f6de055434a33fb09`
- Principal path:
  `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`
- Relevant files inspected:
  - `Lean/ConciseIPRA/PR.lean`
  - `Lean/ConciseIPRA/Syntax.lean`
  - `Lean/ConciseIPRA/Deduction.lean`
  - native/iPRA bi-interpretation files exposing `native_iff_pra` and
    `pra_iff_native`

## Algebraic-number background

- S. Basu, R. Pollack, and M.-F. Roy, *Algorithms in Real Algebraic Geometry*,
  2nd ed., Springer, 2006.

The standalone checker in this archive does not copy code from these sources.
It is original, dependency-free sparse-polynomial verification code for the
identities displayed in the paper.
