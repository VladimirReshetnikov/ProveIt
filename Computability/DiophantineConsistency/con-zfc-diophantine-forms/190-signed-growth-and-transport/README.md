# Signed growth and centered Pell transport for Diophantine consistency

Research prepared for Vladimir Reshetnikov, 25 October 2026.

This package supplies explicitly specified ordinary integer polynomials,
ordinary mathematical proofs of their consistency equivalences, and exact
offline checks of their finite algebra. The central theorem, with the
domain of each polynomial kept explicit, is

\[
\mathrm{ZFC}\vdash
\bigl(\text{the specified equation has no solutions}\bigr)
\longleftrightarrow\mathrm{Con}(\mathrm{ZFC}).
\]

The proof composes the new arithmetic with the precisely identified inherited
refutation calibration. It proves neither consistency nor inconsistency.
There is no newly compiled end-to-end Lean/Rocq proof object, no claim of
global minimality, and no claim of worldwide priority. Independent reviews
in this archive are separate AI-assisted mathematical audits and separate
exact implementations, not external human peer review.

## Results

| Profile | Domain | Variables | Exact degree | Squares | Exact monomials | Other exact cost |
|---|---|---:|---:|---:|---:|---|
| Sparse quartic | unrestricted integers | 209 | 4 | 149 | 5,486 | final height 2^32 |
| Lower-height quartic | unrestricted integers | 209 | 4 | 149 | 6,654 | final height 2^30 |
| Staged pool | unrestricted integers | 130 | 12 | 70 | not expanded | 2,475 binary operations |
| Staged pool | unrestricted integers | 116 | 16 | 56 | not expanded | 2,433 binary operations |
| Four-base pool | unrestricted integers | 107 | 32 | 47 | not expanded | 2,419 binary operations |
| Centered transport | **strictly positive** integers | 10 | 190 | not an SOS presentation | not expanded | 119 binary operations |

The pooled coefficient heights have certified upper bounds `<2^54`, `<2^84`,
and `<2^107`, respectively; these are not exact measured heights. Their
largest literal constant is 2^20. The ten-positive-variable polynomial retains
four enormous fixed coefficients: the largest has 592,884 bits. The operation
counts are arithmetic-gate counts, not bit complexity.

The principal equation is the sum of the squares of the 149 quadratics printed
in Appendix A and stored in `quartic/equations/affine209_F64/equation.json`.
The full collected expansion is provided alongside it. The compact polynomial
is specified completely by 119 ordered arithmetic gates in
`compact/equation.json`; its full formula and finite coefficient recipe are
printed in the report. None of these equation data uses variable exponents,
division, floors, unbounded searches, or implicit predicates.

Against the inspected sources, the quartic removes one variable and one square
from a 210-variable, degree-4, height-2^40 parent. Its sparse version lowers
height by a factor of 256 at a cost of 204 extra monomials. Its second version
lowers height by 1,024 with a larger support. The pooled equations remove one
variable at each matched degree from 131/12, 117/16 and 108/32 source forms.
The compact equation lowers the inspected ten-positive-variable degree from
206 to 190 at a higher operation count. These are measured tradeoffs.

## The new mechanisms

1. **Signed affine horizon.** Replace `t=16+4z^2` by `t=2+4z`. A preliminary
   absolute-value bound and the literal retained `q^t` request recover all
   needed signs before applying the positive-center Pell growth estimate.
   A cofinal binary-residue construction proves completeness. This semantic
   change needs a proof; it is not a coordinate bijection with the old slice.
2. **Integral scaling on the zero set.** Every new integer zero forces
   `v2(F)=20`. Substitution `F=64f` or `F=128f`, followed by an integral
   normalization of one row, therefore has an integral inverse at every zero.
   Two elementary residual-basis operations improve the second height bound.
3. **Whole-product center with stronger low-degree transport.** The transport
   `L=U E b^2` handles the small Pell-index case that defeats bare `b^2`.
   Its cross term has degree at most 184; the center's norm defect then
   determines the exact degree 190.
4. **Oriented reciprocal pooling.** A strictly bounded rational sum of squares
   forces all component errors to vanish. Coprimality of the pool moduli is
   not required. Acyclic unit-pivot elimination then lowers dimension.

The direct quartic and pooling branches use the C222 proof calculus and its
named ZF/ZFC refutation calibration, without simulating K215 or instantiating
Jones's universal expression. The compact branch retains its native/compiler/
K215 ancestry. It is offered as a separate degree improvement.

## Read the report

- `report/main.pdf`: complete research report, proofs, and explicit equations.
- `report/main.tex` and the other `report/*.tex`: editable LaTeX source.
- `report/quartic_residuals.tex`: all 149 principal residuals; checked against JSON.
- `report/compact_coefficients.tex`: complete fixed coefficient recipe.
- `RESULTS.json`: machine-readable result and source hashes.
- `INTEGRATION.md`: suggested repository integration and claim boundaries.
- `PROVENANCE.json`: pinned source and dependency ledger.

## Reproduce

Python 3.10 or newer, standard library only:

```sh
python3 -B verify_all.py --rebuild
```

This runs all three independent equation checkers, parses the printed quartic
coefficients, reconstructs the fixed compact numerals, rebuilds every emitted
equation in fresh temporary directories, and checks the release manifest.
The verification does not search for roots or decide consistency. The unbounded
soundness/completeness arguments are the written mathematical proofs.

To regenerate the printed residuals and PDF:

```sh
python3 -B render_residuals.py
latexmk -cd -pdf -interaction=nonstopmode -halt-on-error report/main.tex
```

The release PDF was rendered and visually inspected. Recompiling the PDF can
change its binary hash because of TeX metadata; that does not change the
equation. A modified release should receive a fresh manifest.

## Source scope

The comparison snapshot is
`d123610bc98fef2006bff1c9466bc3f1221003e7`, including placed packages through
178 and all seven incoming archives present at that commit. The original
210-variable parent was independently replayed from its complete incoming
archive before assembling this package; that receipt is retained. This compact
archive includes the selected inherited proof texts and notices, not every
historical redundant PDF and equation file. Original source URLs and hashes
allow retrieval of the full historical closures.

New material follows the repository's MIT No Attribution license. Retained
third-party notices and licenses remain with the relevant source material.

