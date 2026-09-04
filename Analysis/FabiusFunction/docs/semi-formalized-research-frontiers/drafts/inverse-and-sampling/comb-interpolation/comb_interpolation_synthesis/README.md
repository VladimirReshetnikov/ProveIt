# Comb Interpolation and Sampling Frontiers

This directory is the canonical editorial synthesis of the additive-dyadic and
geometric-comb manuscripts in this part of the Fabius--Rvachev frontier
corpus. The source is organized as one article rather than four adjacent
reports: common interpolation algebra is developed once, genuinely different
extensions retain their own proofs, and repeated statements are represented
by their strongest verified human-readable form.

The immutable editorial baseline is Git revision
`73f0b373126ef22a3b5dccadfa7b99d61d445345`. It is recorded in
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION). All source-disposition and
historical-checksum statements below refer to that revision, not to an
unqualified moving branch.

## What is canonical

- [`comb_interpolation_synthesis.tex`](comb_interpolation_synthesis.tex) is
  the publication driver.
- [`chapters/`](chapters/) contains the proof-bearing geometric core,
  geometric extensions, additive-dyadic theory, reference appendices,
  provenance, and bibliography.
- [`source_disposition.csv`](source_disposition.csv) accounts for all 180
  files in the source-pin subtree: the four pre-synthesis report trees and
  their parent routing README.
- [`post_pin_disposition.csv`](post_pin_disposition.csv) accounts separately
  for all 23 paths added or modified before the mainline reconciliation pin.
- [`assets/`](assets/) contains the unique retained computational evidence and
  the audit of the historical ledgers.
- [`audit/`](audit/) contains the source pin and the deterministic editorial
  tooling. Generated audit products do not replace mathematical proofs.

The source currently distinguishes exact Lean crosswalks from results proved
only in the manuscript. A manuscript theorem label is never, by itself,
evidence of a compiled Lean declaration. Likewise, numerical tables and plots
are checks and illustrations, not proof premises. The current
`FabiusFunction.LagrangeRvachevSynthesis` crosswalk verifies generic scalar
decoder synthesis, node biorthogonality, coefficient factorization, the full
finite interpolation loop, and the unnormalized decoder row-sum law. It does
not claim a formal geometric Gaussian closed-form decoder, the associated
elementary-symmetric/prefactor formula, a `Matrix` wrapper, or decoder
optimization.

The separate exact concordance row maps the strict-interior formula in
`thm:weight-valuation` to `Fabius.twoPowChoose_padicValNat` in
`FabiusFunction.PrimePowerBinomialValuation`. That module also proves the
arbitrary-prime identities `Fabius.primePowerChoose_padicValNat_add` and
`Fabius.primePowerChoose_padicValNat`, including the positive right endpoint
`j = p^m`. The companion proposition is now exact as well:
`Fabius.primePowerSubOneChoose_padicValNat` proves that the full row
`p^m - 1` consists of `p`-adic units,
`Fabius.primePowerSubTwoChoose_padicValNat` proves
`v_p(choose(p^m - 2, j - 1)) = v_p(j)` for the essential strict range
`0 < j < p^m`, and `Fabius.twoPowSubTwoChoose_padicValNat` is the exact
dyadic wrapper used by the endpoint-flat weights.

The exact row for `gq:thm:richardson-generating` maps to
`Fabius.geometricLagrangeRichardson_generating` in
`FabiusFunction.GeometricRichardsonGenerating`. It proves the stated
Euler-coefficient formal-power-series factorization over a field for nonzero
`q`. No root-of-unity exclusion is needed for that totalized algebraic
identity, but interpreting its coefficients as genuine Lagrange
interpolation requires pairwise-distinct nodes. The separate explicit
convolution `Fabius.geometricRichardsonTransform_generating` remains valid
over commutative rings even at `q = 0`, without providing Lagrange
interpolation semantics there. The analytic companion
`Fabius.hasSum_geometricLagrangeRichardson_mul_pow` additionally assumes a
complete normed field, `‖q‖ < 1`, and absolute summability of the normalized
data series.

## Sources reconciled

The earlier `Dyadic_Comb_Frontiers` volume had already absorbed nine nested
manuscript packages: six comb-sum/interpolation reports, two
Euler--Maclaurin/exhaustion reports, and the Bernoulli--Ruffa phase-calculus
report. Its provenance appendix names all nine packages and describes what
each contributed. The duplicate nested manuscript documentation was therefore
not an independent publication layer and has been retired.

This synthesis adds the three formerly standalone geometric-comb manuscripts:

- `geometric_comb_q_fabius_report` supplies the strongest finite
  Gaussian-Pascal, Jackson--Newton, Lagrange-residual, and stability spine;
- `geometric_comb_interpolation_report` supplies modal, Mellin,
  regular-variation, spline, and exact boundary-filter extensions;
- `geometric_comb_interpolation_report-3` supplies complementary arbitrary-
  target, Fabius-transform, reciprocal-product, and asymptotic material.

The documentation layers of all twelve noncanonical source packages (nine
nested additive-dyadic packages and three geometric packages), the old report
TeX/PDF pairs, package wrappers, stale checksum ledgers, and generated preview
PDFs are no longer live publications. Original bytes remain
recoverable from the immutable Git baseline. Scripts, exact tables, data,
text outputs, and PNG figures that remain useful for reproduction are retained
under [`assets/companion-evidence/`](assets/companion-evidence/), grouped by
their historical source slug. One byte-identical dependency file shared by
the two interpolation packages is stored once at
[`assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt`](assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt).

See [`PROVENANCE.md`](PROVENANCE.md) for the editorial chain and
[`assets/VALIDATION.md`](assets/VALIDATION.md) for completed checks and
remaining reproducibility work.

## Build the canonical article

Run from this directory. The publication gate requires exactly three strict,
serial passes after the final TeX edit:

```text
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
```

A successful command is not, by itself, the complete publication gate. From a
clean auxiliary state, the preceding semantic-union source received exactly three
strict serial passes at fixed source epoch `1788242400`, producing 151, 158,
and 158 pages. The retained publication PDF has 158 pages, 2,456,105
bytes, and SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`.
The later canonical-notation edits in `chapters/01_geometric_core.tex`,
`chapters/03_additive_dyadic.tex`, and `chapters/90_reference_appendices.tex`,
together with the document-local geometric-Newton command in the driver, make
that PDF a validated historical checkpoint rather than a rendering of the
current source; a fresh exact three-pass build is pending. The current source
and retained PDF are recorded as distinct receipt facts. The complete
checkpoint receipt and older historical receipts are recorded once in
[`assets/VALIDATION.md`](assets/VALIDATION.md).

## Reproduce the computational evidence

The retained scripts have different dependency sets and output conventions;
there is no single package-wide lock file. Work in a disposable copy or send
outputs to a scratch directory so the reviewed evidence is not overwritten.
The principal exact or quick entry points are:

```text
python dyadic_comb_experiments.py --outdir <scratch-output> --max-level 8
python fabius_dyadic_comb_experiments.py --skip-fractional
python fabius_dyadic_interpolation_experiments.py --mode quick --output-dir <scratch-output>
python numerical_experiments.py --task smoke
python fabius_dyadic_interpolation_experiments.py --outdir <scratch-output> --quick
python fabius_em_experiments.py --output-dir <scratch-output> --max-power 10 --max-level 10
python verify_fabius_rvachev_quadrature.py --max-degree 7 --output-dir <scratch-output>
python experiments.py --output-dir <scratch-output> --grid-power 19 --skip-fft
python geometric_comb_experiments.py --output-dir <scratch-output>
```

Those commands are run from the corresponding source-slug directory under
`assets/companion-evidence/`; several filenames intentionally recur in
different packages. Two geometric scripts have no command-line arguments and
write beside themselves. The complete per-package command map, including the
full interpolation replay, is in [`assets/README.md`](assets/README.md).

## Current status

The 180-row source-pin disposition and 23-row post-pin reconciliation are
complete. The eight historical ledgers contribute 151 audit rows: 68 match
byte-for-byte, 34 match after CRLF/LF normalization, 29 differ substantively,
and 20 point to files no longer present at that pin. These are historical facts,
not a live checksum certificate.

The current source preserves the completed publication union's stable-path edits
in `chapters/01_geometric_core.tex` and `chapters/99_bibliography.tex` together
with the local general-$q$, endpoint-jet, Lagrange-synthesis,
`PrimePowerBinomialValuation`, `GeometricRichardsonGenerating`,
reference-appendix, layout, and driver edits in
`chapters/03_additive_dyadic.tex`, `chapters/90_reference_appendices.tex`, and
`comb_interpolation_synthesis.tex`, and adds the exact generic-prime and dyadic
companion-row valuation crosswalk and Richardson generating-function crosswalk
described above.  It now spells every genuine
two-adic valuation with the shared `\TwoAdicValuation` command and uses the
document-local `\FabiusGeometricNewtonCoefficient{k}{q}` family for the
geometric Newton coefficients formerly homographic with that valuation. The
repository-wide Lean
documentation census recorded at the earlier merge checkpoint was 629 modules
and 8,546 public declarations. That historical census is contextual evidence,
not a claim that every manuscript result in this volume is formalized.

The deterministic validator passes the nine-file TeX graph, structural and
proof discipline (213 result environments, 150 proof-required), 801 labels,
783 references, 62 bibliography keys,
disposition, historical-ledger, companion-payload, 232-row
theorem-concordance gates. Its narrow Lean identifier check is not a live
theorem-type check. No live package-wide checksum ledger is generated or checked
by the current validator. The retired root checkpoint remains recoverable from
Git, but does not certify current package state. A fresh-checkout reproduction
and a full rerun of every retained numerical script remain separate
reproducibility work.
