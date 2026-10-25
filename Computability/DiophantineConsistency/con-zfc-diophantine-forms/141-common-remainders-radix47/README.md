# Common remainder certificates for Diophantine consistency

Prepared for Vladimir Reshetnikov / ProveIt, 25 October 2026, with AI assistance.

## Principal result

`direct/equation/equation.json` defines a fixed quartic in **252 unrestricted
integer variables** as the sum of squares of **182 quadratic or affine
residuals**. `direct/equation/expanded_polynomial.json` supplies every one of
its **5,340 nonzero collected coefficients**. The coefficient height is
**128,446**.

The ordinary theorem, composed with the pinned C222/refutation calibration,
is that ZFC proves its integer unsolvability equivalent to Con(ZFC). The
new arithmetic argument replaces eleven separate remainder intervals by one
norm bound at a common denominator. It removes **30 variables and ten rows**
from the newest matched 282-variable direct quartic, preserves degree and
coefficient height, and removes 151 collected monomials. This direct route
does not encode K215 or instantiate Jones's universal polynomial.

This is not a global minimality result, a proof of consistency, or a newly
compiled end-to-end Lean/Rocq certificate. The report distinguishes the new
proof, exact finite verification, and retained unbounded proof dependencies.

## Read the research

- `report/report.pdf`: full article, including the complete 182-residual
  polynomial specification in an appendix.
- `report/report.tex` and its adjacent `.tex` inputs: complete LaTeX source.
- `direct/proofs/NORMALIZED_REMAINDERS_PROOF.md`: detailed proof of the main
  transformation.
- `direct/proofs/INDEPENDENT_REVIEW.md`: separate mathematical audit.
- `radix49/radix49/radix49_completion.md`: exact finite completion of the
  repository's previously conditional shared-marker radix49 construction.
- `compact/DENOMINATOR_PROOF.md`: smaller carrier denominators for the
  ten-positive-variable compact equations.
- `radix47/radix47/radix47_proof.md`: full new complemented-label radix47
  encoding proof; its coefficient tuple takes 207,214 raw bytes.
- `radix47/radix47/equation.pdf`: complete one-page formula with its closed
  coefficient specification.
- `RESULTS.json`: exact final result inventory, with domains kept separate.
- `INTEGRATION.md`: proposed repository placement and scope of the changes.

Any additional native-radix component has its own complete proof, coefficient
tuple, ordinary review, and independent finite verifier. The report and
`RESULTS.json` identify the achieved profile of every released component.

## Verify

The arithmetic verification uses only the Python standard library. From the
archive root:

```sh
python3 -B direct/code/verify.py
python3 -B -O direct/code/verify.py
python3 -B direct/code/verify.py --rebuild
python3 -B radix49/verify_radix49.py
python3 -B radix47/verify_radix47.py
python3 -B radix47/audit_radix47_peer.py --root radix47
python3 -B compact/verify.py
python3 -B verify_release.py
```

The direct optional rebuild compares nineteen generated JSON artifacts byte
for byte in a temporary directory. It does not need the repository or a
network connection. The independent checker covers all source changes,
18 inherited Horn factoring edits, 205 integral monic projections, the
final translation, and every collected quartic coefficient. Seven corrupted
artifacts are rejected in both ordinary and optimized Python.

The top-level verifier checks the sealed file inventory, exact result
metadata, and agreement of the printed appendix's source with the final
equation. It is a finite audit, not a proof of the unbounded semantic theorem.

## Build the article

With a standard TeX Live installation:

```sh
cd report
python3 generate_appendix.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The appendix generator reads the final JSON polynomial; it introduces no
new coefficients. The delivered PDF has been rendered and visually checked.

## Exact source snapshot and attribution

The comparison snapshot is ProveIt commit
`55d1f72aedebf892e446c90d35fa1ae37689b0f2`, including the incoming
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip` and
`ConZFC_Certificate_Reductions_2026-10-25.zip` archives. The delivered
packages preserve source-file and archive hashes and relevant inherited
proof texts. No repository mutation is part of this deliverable.

The common-remainder construction is the new main mathematical contribution.
The radix49 encoding and its conditional carry proof are prior repository
work; their finite completion is attributed accordingly. Bit complementation,
Pell methods, and the product-square finalizer have identified predecessors.
Claims of improvement are relative to the inspected sources, not assertions
of literature-wide priority.

New material follows the repository's MIT No Attribution license. Copied
material retains its original notices. No human review or institutional
endorsement is implied by the independent AI-assisted reviews.
