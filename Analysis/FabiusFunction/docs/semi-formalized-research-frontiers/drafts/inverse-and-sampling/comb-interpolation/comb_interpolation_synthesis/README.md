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
finite interpolation loop, and the unnormalized decoder row-sum law. The
companion `FabiusFunction.LagrangeRvachevMatrix` API adds
`rvachevAtomIndexSet`, `RvachevAtomIndex`,
`lagrangeRvachevEncoderMatrix`, and `lagrangeRvachevDecoderMatrix`, together
with `lagrangeRvachevEncoderMatrix_nonneg`,
`sum_lagrangeRvachevEncoderMatrix_row_eq_one`,
`sum_lagrangeRvachevDecoderMatrix_row_eq_one`, and
`lagrangeRvachevEncoderMatrix_mul_decoderMatrix`. These declarations exactly
discharge `gq:thm:gaussian-Appell-biorthogonality`. The generic
`exists_neg_entry_of_rightInverse_of_row_overlap` and its specialized
`exists_lagrangeRvachevDecoderMatrix_entry_neg_of_row_overlap` prove the
negative-entry conclusion only when the stated strictly positive row overlap
is supplied. The downstream one-definition/fourteen-theorem
`FabiusFunction.RvachevAppellHasse` module now proves the generic finite
Appell--Hasse transform, odd reciprocal-moment parity, the even Rvachev--Hasse
formula, the q-falling elementary-symmetric specialization, and the explicit
geometric Lagrange--Rvachev decoder. In particular,
`eval_rvachevDeconvolvedPolynomial_qFallingPower`, combined with the existing
finite polynomial synthesis theorem, exactly discharges
`gq:prop:q-Appell-falling`, while
`geometric_lagrangeRvachevDecoder_eq`, combined with the generic scalar
cardinal synthesis, exactly discharges
`gq:thm:gaussian-Appell-decoder`. The algebraic formulas are totalized at zero
or colliding nodes, but cardinal semantics use the manuscript assumptions
`0 < q < 1` and `c > 0`; Lean writes the Gaussian power with the equivalent
nonnegative denominator exponent. This promotion does not add an analytic
reciprocal-MGF series theorem or a decoder-optimization result.

The 232-row concordance therefore records 7 Lean-proved rows, 159
human-proved frontier rows, 20 conjectures, 30 open problems, and 16 rows for
which proof status is not applicable. Its source projection and total row
count are unchanged.

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

A successful command is not, by itself, the complete publication gate. The
accepted merged-source receipt is root
`187L/6724B/a4c1e33165ff7291682cd890f23fe4af98e9f11f7ad1d9a7f8b68c78d53f9a56`,
nine-file graph
`12773L/483551B/cef466ee56f6bb864faaac2244bccf1dbc2fd4032a717b6c81604551c0427309`,
passes `153/160/160`, PDF
`160pp/2468109B/bb714c8be4b82de2a888e0302da3aaf957b9e885f2c5f59466b3ea5d659e3f71`,
and final log
`1370L/58773B/8df53a7db51c85b7a046c5f58587319095b3d28c61b0091861bdeb1f43b342e3`.
Every recorded prohibited-log, A4/rotation, PDF 1.5, encryption, font/subsetting,
Libertinus, Type-3, and visual gate passed.

For explicit history, the preceding semantic-union source received three
strict serial passes at fixed source epoch `1788242400`, producing 151/158/158
pages. Its 158-page, 2,456,105-byte PDF had SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`.
The later canonical-notation edits in `chapters/01_geometric_core.tex`,
`chapters/03_additive_dyadic.tex`, and `chapters/90_reference_appendices.tex`,
together with the document-local geometric-Newton command in the driver, make
that PDF a validated historical checkpoint rather than a rendering of the
current source. The former root
ledger recorded the source and retained PDF as distinct payloads at its
historical checkpoint. The complete
checkpoint receipt and the older historical receipts are recorded once in
[`assets/VALIDATION.md`](assets/VALIDATION.md).

The current synchronized `b899` driver has 187 lines and 6,724 bytes, with
SHA-256
`a4c1e33165ff7291682cd890f23fe4af98e9f11f7ad1d9a7f8b68c78d53f9a56`.
Its 15-file recursive TeX closure has 12,597 lines and 477,163 bytes, with
digest `9e22455b3f65eb48306ad21c57445b6052a56498cb363666ffb9b160f5cc8090`.
Exactly three passes from absent sidecars ran 153 pages / 2,383,950 bytes →
160 / 2,467,995 → 160 / 2,468,000. The final 160-page, 2,468,000-byte PDF
has SHA-256
`ad8587049580e6fde371f534b6f8b4e56fa4c929173f87d3021ed369e5225d4c`.
All 160 pages are A4 at rotation zero, render successfully, and contain nonblank
text. All 33 font rows are embedded and subset, seven are Libertinus, and none
is Type 3. Log, metadata, visual, cleanup, and forbidden-basename gates passed,
with no overfull box.

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
`RvachevAppellHasse`, reference-appendix, layout, and driver edits in
`chapters/03_additive_dyadic.tex`, `chapters/90_reference_appendices.tex`, and
`comb_interpolation_synthesis.tex`, and adds the exact generic-prime and dyadic
companion-row valuation crosswalk, Richardson generating-function crosswalk,
and q-Appell/geometric-decoder crosswalks described above.  It now spells every genuine
two-adic valuation with the shared `\TwoAdicValuation` command and uses the
document-local `\FabiusGeometricNewtonCoefficient{k}{q}` family for the
geometric Newton coefficients formerly homographic with that valuation. The
repository-wide Lean
documentation census recorded at the earlier merge checkpoint was 629 modules
and 8,546 public declarations. That historical census is contextual evidence,
not a claim that every manuscript result in this volume is formalized.

The deterministic validator checks the nine-file TeX graph, structural and
proof discipline (213 result environments, 150 proof-required), 801 labels,
783 references, 62 bibliography keys,
disposition, historical-ledger, companion-payload, 232-row
theorem-concordance gates. Its narrow Lean identifier check is not a live
theorem-type check. No live package-wide checksum ledger is generated or checked
by the current validator. The retired root checkpoint remains recoverable from
Git, but does not certify current package state. A fresh-checkout reproduction
and a full rerun of every retained numerical script remain separate
reproducibility work.
