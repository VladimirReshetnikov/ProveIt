# Provenance ledger

## Current five-publication synthesis

This canonical package combines material from two former, coequal canonical
publications and three retired general-guide donors. The immutable
pre-retirement snapshot of all five source packages is commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`, recorded in
`audit/MERGE_SOURCE_REVISION`; the completed `source_concordance.csv` gives a
reviewed disposition for all 547 source result environments. This immutable
merger ledger's canonical-status distribution remains 74 Lean-proved rows,
404 human-proved frontier result rows, 60 not-applicable rows, and 9
conjecture rows.
Directory names
in the table are historical paths in that pinned snapshot, not live package
paths.

| Historical source package | Role in this synthesis |
| --- | --- |
| `q_pochhammer_q_binomial_monograph/` | Forward algebraic, combinatorial, analytic, arithmetic, geometric-interpolation, Thue--Morse, and Fabius--Rvachev backbone. |
| `inverse_q_analogs_and_series/` | Universal and branch-aware inversion, asymptotic transfer, certification, inverse observables, five labelled conjectures, and the six-package provenance/assets preserved below. |
| `general-q-series-guides/q-series-proof-oriented-article/` | Donor of stronger or independent very-well-poised, theta/modular, sums-of-squares, Bailey, and continued-fraction material. |
| `general-q-series-guides/q_series_from_first_principles/` | Donor of the general Bailey parameter-lowering step and full Andrews--Gordon theorem. |
| `general-q-series-guides/q_series_monograph/` | Donor of exact eta asymptotics, coefficientwise-limit, Borwein-reciprocity, and selected frontier material after correction. |

The three guides arrived respectively in commits
`1360db6064c676f83bceb23bece5ed304dd09ce8`,
`c167e550348bfb33b4297684100d55dfb48b8c1a`, and
`1f0f98390d551725fc7d2274638dbd7de86ee346`. They had no unique non-document
assets: each donor package consisted only of TeX, PDF, and a historical digest
receipt. Their superseded PDFs were retired with the donor packages
and are not canonical renderings of this larger source. The former forward
and inverse manuscript PDFs were removed for the same reason. The merged
master records an earlier historical source-pinned publication receipt: a
reproducible 335-page A4 artifact built from the then-current source SHA-256
`9b7ac11a815efa7f3c6ea08b9626c06143fd6b0d633fef6edfc8bc21c2f6783a`
by exactly three successful serial passes at fixed source epoch `1788242400`.
The build gate pinned `origin/main` at
`8a7d03dc379638a6cbda302074b2feba27c21961`; the 2,163,339-byte PDF has
SHA-256
`91c649d0c69628e134e71f1be6c39c3cbc96b91bfc63e456011083cf0e882f03`.
That earlier receipt remains provenance for its named source only. A later
validated historical checkpoint was a reproducible 340-page A4 artifact built
from source SHA-256
`da420f5b2622cd088af43cea0ac448105c9f6af65cf1734de6535e3427f8e052`.
The 2,180,191-byte PDF has SHA-256
`e64a4ef65a9fcce3a4f211f2125b0f8440910cf4527635f76975b0967800e667`.
It too remains provenance for its named source only.

A subsequent upstream publication receipt records a historical 378-page A4
PDF of 3,175,603 bytes, with SHA-256
`5d0dac5a8d1cba7bedab9055a51f59478054de22969dcf75b0f58ce3f3c265bc`, built
in three serial passes from a 15,630-line, 764,952-byte source with SHA-256
`403a25dccadc15e7a34bedd8d28a2dc3369cb6e6a046cd199a30ed178742a32d`.
That receipt remains provenance for its named historical source only.

The current canonical publication was rebuilt on 2026-09-03 from clean
auxiliaries at fixed source epoch `1788495770`. Exactly three successful
serial `pdflatex -interaction=nonstopmode -halt-on-error` passes produced 386,
395, and 395 pages, with `imakeidx` successfully generating the index during
each pass. Its 16,834-line, 837,715-byte source has SHA-256
`d8f730b8eb6602d4d16112aea77a3e67dfbeadf46bcd28c1cdf3b12450b7d4fb`;
the current 395-page, 2,494,949-byte A4 PDF has SHA-256
`5d25df07e6df1cd32118ee87e64c1cc54ad32da7c578a182231f98dd9fee9d5c`.
Every page is rotation zero, rendered successfully, and nonblank; all 43 font
rows are embedded and subset Type 1 fonts, five are Libertinus, and none is
Type 3. Title, author, subject, and keyword metadata are present. The final log
has no TeX or package warning, undefined reference or citation, duplicate
destination, or rerun request. Its one 32.5659 pt overfull paragraph was
visually checked on physical page 17 and is readable and unclipped. The
validation record in `README.md` gives the complete page-render and visual
sample receipt. No live checksum manifest is maintained. PDFs retained beneath
`assets/` are research figures, not manuscripts.

The current source incorporates exhaustive crosswalks for
`QPochhammerEntire` (zero definitions and five legacy compatibility theorems),
`QPochhammerInfinite` (one definition and twenty-nine theorems),
`QPochhammerDissection` (zero definitions and two theorems),
`GaussianBinomialPalindromic` (zero definitions and fourteen theorems),
`GaussianBinomialPolynomialStructure` (zero definitions and five theorems),
`GaussianBinomialBounds` (zero definitions and six theorems), and
`GeometricPochhammerNormalConvergence` (zero definitions and three theorems).
It also inventories `QMultinomial` (one definition and nine
theorems), `QuantumMultinomial` (zero definitions and five theorems),
`QPochhammerInfiniteBounds` (zero definitions and five theorems),
and `QPochhammerComplexOrder` (one definition and four theorems),
`BasicHypergeometricSeries` (two definitions and five theorems),
`HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems). The next tranche adds
`QExponential` (three definitions and eight theorems), `JacksonIntegral` (one definition and seven
theorems), `ThetaQuasiPeriodicity` (one definition and six theorems),
`QPochhammerLogDerivative` (zero definitions and ten theorems),
`QPochhammerOrderDerivative` (zero definitions and three theorems), and
`JacobiCubic` (zero definitions and two theorems). The current tail adds
`CentralQBinomialReduction` (zero definitions and six theorems) and
`CyclotomicFactorization` (zero definitions and seven theorems), followed by
`CyclotomicDivisibility` (zero definitions and three theorems),
`PrimitiveRootBlock` (zero definitions and three theorems), `QCatalan` (one
definition and eleven theorems), and `QLucas` (zero definitions and seven
public theorems; its copy of `two_mul_choose_two` is private because the public
name is owned by `QChuVandermonde`). The latest tail adds `QBetaIntegral` (one
definition and eight theorems) and `NewtonInterpolation` (three definitions
and nineteen theorems),
followed by `GaussianBinomialInteger` (one definition and ten theorems),
`GaussianBinomialComplexOrder` (one definition and five theorems), and
`QPfaffSaalschutz` (zero definitions and three theorems), together with
`GaussianBinomialBounds` (zero definitions and six theorems). The
`QPochhammerEntire.lean` leaf proves the fixed-nome
single-symbol locally uniform product and differentiability, the
division-free factor-zero criterion including `q = 0`, the reciprocal-power
zero lattice for nonzero nome, and simple analytic order at every zero. The
public `complexQPochhammerInf_eq_qPochhammerInfIn` bridge is an unconditional
definitional equality for every complex parameter and nome; it makes no
convergence claim. The generic `QPochhammerInfinite.lean` surface now owns actual derivative
nonvanishing from every raw factor equation, including `q = 0`, and analytic
order exactly one at every zero; `QPochhammerEntire.lean` preserves the legacy
complex-wrapper naming surface. Only `thm:poch-entire` is promoted by those
single-symbol results. The newer three-theorem leaf proves
the additional outer product's local-uniform (normal) convergence for every
complex strict contraction, including `q = 0`, and gives the dyadic Rvachev
product and bounded-Fabius Fourier specializations. The compound
`thm:qF-spectral` row remains Partial because its named centered/MGF packaging
and exterior reciprocal, pole-divisor, and zero--pole clauses are absent. The
forward status inventory covers 282 labelled results: 166 Exact / 90 Partial /
18 None / 8 N/A; the 191-result pre-Fabius core remains 36 / 29 / 123 / 3.
The five-publication concordance
has 74 Lean-proved, 404 human-proved frontier, 60 not-applicable, and 9
conjecture rows. The `cor:positivity`, `thm:qbinom-structure`, and
`prop:gq-positive-palindromic` rows are Exact: both Gaussian structure APIs
support the structure row, and the fourteen-theorem generic API now gives
the strict-interior coefficient-of-`q` formula and all boundary zeros. The
central-reduction row is Exact through its division-free commutative-ring
identity and field quotient wrapper. The cyclotomic-factorization row is Exact
for the factorial form over every commutative ring and the Gaussian form over
every integral domain, with the exponent bounds explicit. The complete root
block, square-free cyclotomic criterion, and q-Catalan row are Exact. The
evaluated primitive-root q-Lucas identity is formalized, but `thm:q-lucas`
remains Partial because its polynomial congruence modulo `Φ_d(q)` has no Lean
counterpart. The primitive-root value in the Babbage corollary is
formalized, but its derivative clause keeps that compound row Partial. The
half-base Gaussian valuation row remains Partial because its concluding
odd-integer valuation statement has not yet been formalized. The q-beta integral and
recurrence rows are Exact on their stated positive real domain, and the
geometric Newton and triangular-coefficient rows are Exact through the generic
field-valued interpolation module and its geometric-grid specialization. The
terminating q-Pfaff--Saalschütz row is Exact under its explicit denominator
hypotheses; the integer-index Gaussian identities and reciprocal series and
the two complex-order series rows are also Exact on the domains recorded in
the crosswalk, while the separate complex-parameter property rows remain
unformalized. The quantum-multinomial row is Exact over every semiring under
the displayed q-commutation hypotheses, without assuming that q is central or
that the ambient semiring is commutative. `GaussianBinomialBounds` reuses
`finiteQPochhammerIn_self_pos` from `GeneralQConditionNumber` and supplies
evaluated reciprocity and the finite growth bounds on both sides of `q = 1`;
the imported positivity theorem is not counted as a declaration of the
bounds leaf. Its six exported theorems close the exact finite-growth row, while
the greater-than-one compound row remains Partial only at its asymptotic
clauses. No PDF was generated locally while resolving this merge; the retained
artifact remains a historical publication checkpoint and does not render the
current source.

The former q-Pochhammer/q-binomial monograph arrived in commit
`47172bc03ec078961d8b023dfe156ecd712efb65`. Its pre-repair source SHA-256 was
`9c6aec1066e71bedc612703c12d29b44d44e166e3d72a25566b86d89291c95be`;
the detailed seven-sibling consolidation and correction history remains in the
repository draft manifest. The completed five-publication concordance is kept
separate from the older inverse-source concordance so neither immutable audit
domain is silently reinterpreted.

## Five-publication result inventory

`audit/extract_merge_sources.py` inventories every theorem-style environment
from the five source publications at `audit/MERGE_SOURCE_REVISION`. The pinned
snapshot contains exactly 547 environments:

| Historical source package | Result environments |
| --- | ---: |
| `q_pochhammer_q_binomial_monograph/` | 276 |
| `inverse_q_analogs_and_series/` | 103 |
| `general-q-series-guides/q-series-proof-oriented-article/` | 63 |
| `general-q-series-guides/q_series_from_first_principles/` | 43 |
| `general-q-series-guides/q_series_monograph/` | 62 |
| **Total** | **547** |

By source kind these are 237 theorems, 76 propositions, 50 lemmas, 114
corollaries, 45 definitions, 10 examples, 7 conjectures, 6 problems, and 2
algorithms. The immutable ten-field source projection has SHA-256
`f2e8eb72de37e7f0e05e1d9bee126ebe369cd96ed7882c75ddbdf1015d9494a4`.
Every one of the 168 guide rows has a reviewed disposition and an explicit
canonical destination label. This includes historical-status destinations for
the retired Borwein-sign conjecture and the donor's already-developed
bilateral-Bailey-lattice prompt.

The same extractor generates all thirteen concordance columns, not only the
immutable ten-column source projection. Its default mode exact-compares every
generated editorial decision with the checked ledger. The explicit
`--write-reviewed-csv` mode uses only the pinned revision, requires every
override selector to match exactly once, validates a temporary serialization,
and atomically installs the result. Thus later deduplication redirects and
historical literature dispositions are reproducible rather than hidden manual
edits.

The concordance is deliberately result-level: it does not pretend to be a
byte archive of repeated proof prose, remarks, formula tables, bibliographies,
or publication renderings. The pinned Git revision supplies that complete
archival role. The canonical source supplies the reviewed statements, strongest
proved forms, complete retained proofs, useful explanatory material, and
precisely delimited open problems.

Before donor retirement, a separate semantic audit covered all 23 guide
remark environments, 96 section or subsection headings, five longtables, and
53 bibliography entries, rather than relying on theorem extraction alone. It
identified and transferred fifteen non-theorem product-identity source records,
their exact finite quality-control boundary, the missing Rogers--Ramanujan and
Andrews--Gordon formula-atlas entries, six compact proof or discovery insights,
and the literature needed to correct two outdated open-status claims. The
remaining convergence ledgers, notation indexes, proof-completeness tables,
central formula rows, and repeated explanations were represented by stronger
canonical statements or existing dependency and formalization appendices.

The remainder of this ledger preserves the earlier six-package inverse-q
consolidation. Historical names, archive hashes, source paths, and the pinned
revision are facts about that prior merge and deliberately remain unchanged.

The canonical volume absorbed the following six source packages.  The paths
below are historical paths relative to their former sibling layout under
`exponents-and-q-series/`.  The exact normalized source tree is pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION), and repository history
preserves every retired path.

| Source package | Canonical role |
| --- | --- |
| `inverse_q_analog_functions_report/` | Branchwise narrative, parameter selection, real and complex branch atlases, numerical continuation. |
| `inverse_q_analog_jet_atlas/` | Universal inverse jets, Bell-polynomial organization, mixed derivatives, Lagrange-Good inversion, coefficient atlases. |
| `inverse_q_analogs_extended_report/` | Corrected special regimes, certification arguments, radial inverses, and Fabius-Rvachev recovery material. |
| `inverse_q_analogs_report/` | Discriminant and remote-branch analyses, interval and continuation certificates, early conjecture register. |
| `inverse_q_analogs_report-2/` | Independent branch synthesis, reciprocal regimes, compact coefficient tables, algorithmic cross-checks. |
| `q_pochhammer_q_binomial_expansions_report/` | Canonical forward expansion engine for finite and infinite products, Gaussian and multinomial coefficients, roots of unity, and q-special functions. |

## Intake archive provenance

All six packages arrived on 2026-08-30.  These hashes identify the submitted
archive bytes, before repository normalization or later editorial changes.

| Historical package | Delivered archive | Outer SHA-256 |
| --- | --- | --- |
| `inverse_q_analog_jet_atlas/` | `inverse_q_analog_jet_atlas_2026-08-30.zip` | `9c9a0353eb355e6defb87845c4a2a79d85c537fe5a6c38c5473f9d3d56448ead` |
| `inverse_q_analog_functions_report/` | `inverse_q_analog_functions_report.zip` | `19cc7da37f71ddbbc0c46b91c55c23059a1e305500260bd0a306394f4c21f4de` |
| `inverse_q_analogs_extended_report/` | `inverse_q_analogs_all_parameters_report.zip` | `0263542a7a6a50459eeb0359015b4086245e7311528e80e3875657529825669f` |
| `inverse_q_analogs_report-2/` | `inverse_q_analogs_report_bundle.zip` | `82ab1dc2cbdd4e69d638cfc045d9ca331e8152e1faeba763732fa9231578b875` |
| `inverse_q_analogs_report/` | `inverse_q_analogs_report.zip` | `471ee715022df77f2c5f45b86c213e50e980478eee1a6fc48dd91556cdaeb627` |
| `q_pochhammer_q_binomial_expansions_report/` | `q_pochhammer_q_binomial_expansions_report.zip` | `e8c6e5be4512abc0bacfd904e3f0027b35fd5e47e916a6ad11cc76b2893b3a07` |

The archive hashes identify delivery bytes.  `theorem_concordance.csv`
records normalized result-level provenance, `assets/ASSET_DISPOSITION.csv`
records path-level disposition, and `audit/SOURCE_REVISION` pins the immutable
pre-retirement Git tree used by the source extractor.

The source packages were independently delivered reports, not a linear series
of editions.  Shared titles or formulas therefore do not imply ancestry.  The
concordance records semantic provenance per result rather than selecting a
single package wholesale.

## Post-retirement audit reconciliation

The later integration commit `53c431137` replayed seven audit-only sidecars
from an older branch into the already retired paths
`inverse_q_analogs_report/` and
`q_pochhammer_q_binomial_expansions_report/`.  They contained no new theorem
statement, proof, TeX source, PDF, experiment program, figure, or numerical
payload.  Their nonduplicative evidence was reviewed and is preserved here;
the redundant sidecars were then retired again so that the canonical package
remains the sole live inverse-q document.

For `inverse_q_analogs_report/`, the sidecars confirm that the original
17-file delivery matched the archive hash already recorded above.  No
submitter-provided digest receipt existed; a repository arrival audit recorded
digests for all 17 payloads before normalization.  Twelve agree with the
pinned normalized snapshot, while five CSV digests differ solely because the
arrival audit preserved their pre-normalization line endings.  A later
normalized edition passed three
strict serial pdfLaTeX runs, a complete 51-page visual inspection, and
deterministic replay of all seven textual data outputs.  That edition had TeX
SHA-256
`de375ee059e0ee9485286aea13e917363854d610b5ff77672001828fa663699b`
and PDF SHA-256
`1ef95365aa42fc5426dc7f7533096ecdc9605479fa1eb6c2b8757fc25e086fdb`.
The superseded source and rendering are recoverable at commit `444cd6ac2`.
Its repaired endpoint, safeguarded-Newton, near-unit truncation-cost, and
conditional-radicals statements are represented in the source concordance and
the corrected canonical proofs.  The late audit's stronger assertion that the
order-five Maxwell collision was proved is not promoted: it treats a large
secondary-discriminant factorization as exact symbolic output without a
retained certificate.  The canonical *Finite q-Pochhammer inversion* chapter
proves the elementary uniqueness statement for the displayed reciprocal
polynomial but correctly keeps the Maxwell-factor identification uncertified.
The exact reship
`Fabius_Rvachev_Frontier_Report_2026-08-30-E.zip`, with outer SHA-256
`174bf733156cd874cf4f9321c6ab71ca44f311856cc01dc158ddf83dc00cf813`,
was byte-identical to the filed package after documented line-ending
normalization and introduced no additional mathematical content.

For `q_pochhammer_q_binomial_expansions_report/`, the sidecars confirm a
seven-file normalized digest audit, exact replay of the retained 44-line numerical
output, three clean serial pdfLaTeX passes, and visual inspection of the
39-page report.  The validated source had SHA-256
`2d3d47cb82ebeea01d43858599e78ddff3d0c97ac62cbe4f09e3ad7314eb4aee`
and its PDF had SHA-256
`88f8e5b4272a949a0521561d2328eb8312167726fbad5c80088ee017921463c5`.
The superseded source and rendering are recoverable at commit `1d5c97985`.
The retained program and numerical output already live in the canonical asset
tree.  These seven late sidecars are intentionally absent from the 77-row
asset-disposition ledger.  That ledger's 73 tracked source hashes are frozen
against asset snapshot `f46e5d7f6f225bf0a43d8945e67d6f0e4aec8d54`, where
all 73 match.  The separate theorem/source-concordance pin
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838` matches only 66 of those 73 asset
rows.  Git commit `53c431137` remains the byte-level archive for all seven
sidecars summarized in this section.

For that reason the earlier six-package consolidation chose the neutral
`inverse_q_analogs_and_series/` directory: promoting the broadest precursor in
place would have falsely suggested that its five peers were merely earlier
editions. The wider merger initially used the similarly neutral
`q_series_and_inverse_analogs/` name. Commit
`7a002460dabbd2094f11be980f4929e2506ec022` then placed exact copies of the
master and PDF at the previously published `q_pochhammer_q_binomial_monograph/`
URL as a temporary compatibility measure. The canonical package now occupies
that published path directly, so the stable URL and the live repository
identity agree. The same-stem path beneath `q-pochhammer-and-inversion/` remains
only a historical source location in the pinned pre-retirement snapshot.

## Source-result inventory

`audit/extract_source_results.py` inventories every theorem-style source
environment from the pinned pre-retirement Git revision.  The six inventoried
snapshots contain 260 such environments:

| Kind | Count |
| --- | ---: |
| theorem | 131 |
| proposition | 28 |
| lemma | 2 |
| corollary | 16 |
| conjecture | 32 |
| problem | 9 |
| research problem | 19 |
| principle | 4 |
| definition | 9 |
| algorithm | 5 |
| computational result | 1 |
| example | 4 |

The generated `theorem_concordance.csv` retains source package, path, line,
label, result kind, title, enclosing chapter and section, and whether a proof
environment followed the statement.  Editorial columns then record the
canonical label, proof status, Lean counterpart when one exists, and the
reason for merging, correcting, retaining, or retiring the source item.

## Non-TeX asset audit and migration

At the pinned pre-retirement revision, the six packages contained 65 tracked
non-TeX files totalling 5,832,780 bytes:
six Python experiment programs, two requirements files, six READMEs, six
historical digest manifests since retired, six generated report PDFs, twenty generated figures, and
nineteen generated data or audit files.  Four additional untracked files in
the forward-expansion package are ordinary `.aux`, `.log`, `.out`, and `.toc`
build intermediates.

Every historical digest in those six manifests matched its corresponding file
at that revision.  SHA-256 comparison found no byte-identical pair among the
69 tracked and untracked non-TeX files.  Similar names therefore did not
license deletion:
for example, the three scripts named `inverse_q_analogs_experiments.py`, the
two PDFs named `inverse_q_analogs_report.pdf`, and the two
`qgamma_inverse_branches.pdf` figures all have different contents.

Only two source packages themselves recorded an immutable repository snapshot:

- `inverse_q_analog_jet_atlas/` records
  `1cea73234a363ddbc392816f6babb5a57920e984`;
- `inverse_q_analogs_extended_report/` records
  `23b19a515ceb44a513b1ec56aeb5c9e99dda5952`.

Both names resolve to commits in the repository.  The other four packages
recorded no package-local immutable source commit, so their build statements are preserved
as historical package claims, not promoted to current validation evidence.
Independently, the theorem/source-concordance audit pins the normalized sources
of all six packages at
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`, the value stored in
`audit/SOURCE_REVISION` and verified as an ancestor of the retirement commit.

Unique scripts, captured outputs, tables, and figures were migrated under
`assets/` when they support a retained theorem, conjecture, or reproducible
calculation.  The completed 77-row disposition ledger retains 39 files---six
programs, 19 CSV/TXT outputs, and 14 vector figures---and retires 38
superseded narratives, duplicate previews, package metadata files, generated
LaTeX fragments, and build products.  It records an immutable source SHA-256
for each of the 73 tracked source files, a canonical destination SHA-256 for
every migration, `NOT_RETAINED` for every retirement, and
`UNTRACKED_TRANSIENT_ABSENT` for the four ignored TeX build paths that did not
exist at the freeze.  All 33 retained non-script payloads match their
historical source bytes.  Exactly five of the six migrated programs carry
distinct destination hashes because their output paths were adapted to the
canonical layout; the forward `q_expansion_experiments.py` stayed
byte-identical because it writes only to standard output and required no path
rewrite.  The programs were rerun serially;
[`assets/VALIDATION.md`](assets/VALIDATION.md) records exact-output parity and
the one disclosed last-digit runtime drift. Repository history preserves the
post-migration digest receipts; no live checksum manifest remains.

All six superseded directories were removed from the live tree.
All tracked superseded material remains recoverable from Git history.  The
only untracked files removed with the old directories were four disposable
TeX build intermediates (`.aux`, `.log`, `.out`, and `.toc`) already recorded
as retirements in the asset-disposition audit.

## Scope boundaries with neighboring volumes

This synthesis is canonical both for forward q-algebra, combinatorics,
summation, arithmetic, interpolation, and Fabius--Rvachev product theory and
for branch-specified inverse maps, singular inverse regimes, certification,
and the six-package concordance above. The former historical package at
`q-pochhammer-and-inversion/q_pochhammer_q_binomial_monograph/` is now its
forward backbone rather than a separate neighboring publication.

`Cyclotomic_q_Fabius_Rvachev_Frontier/` remains a separate natural-boundary
and blow-up volume. Its radial root-of-unity layer overlaps
[*Infinite q-Pochhammer inverse geometry*](chapters/03_infinite_q_pochhammer.tex)
and
[*Cyclotomic and Fabius--Rvachev recovery*](chapters/06_cyclotomic_fabius.tex),
but its condensation, Gould--Hopper, polyharmonic, and natural-boundary
programs are broader than inverse-q branch theory. Likewise,
`Exponents_and_q_Series_Frontiers/` owns the geometric-uniform/Fabius
deformation and signed/reciprocal parameter-orbit program, and
`inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/` owns
the detailed interpolation and stability theory behind the short
geometric-comb application in
[*Cyclotomic and Fabius--Rvachev recovery*](chapters/06_cyclotomic_fabius.tex).
These explicit boundaries prevent the six-source concordance from being
misread as a claim to have absorbed those broader volumes.
