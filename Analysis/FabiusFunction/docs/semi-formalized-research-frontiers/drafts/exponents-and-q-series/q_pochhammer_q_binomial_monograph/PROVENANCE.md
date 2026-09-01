# Provenance ledger

## Current five-publication synthesis

This canonical package combines material from two former, coequal canonical
publications and three retired general-guide donors. The immutable
pre-retirement snapshot of all five source packages is commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`, recorded in
`audit/MERGE_SOURCE_REVISION`; the completed `source_concordance.csv` gives a
reviewed disposition for all 547 source result environments. Directory names
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
assets: each donor package consisted only of TeX, PDF, and a repository
checksum ledger. Their superseded PDFs were retired with the donor packages
and are not canonical renderings of this larger source. The former forward
and inverse manuscript PDFs were removed for the same reason. The merged
master retains one canonical publication checkpoint,
`q_pochhammer_q_binomial_monograph.pdf`: a reproducible 347-page A4 artifact
built from the then-current 14,072-line, 656,200-byte source with SHA-256
`062b7230d95ff8bd52b11253c6c3c8820d6f6a82e4307ae5d82a1d793c00c517`.
Exactly three guarded serial passes produced 337, 347, and 347 pages. The
2,996,319-byte PDF has SHA-256
`29b422a39c42be37bd1487d4245c44e55706720c545dd015957644e47014bd48`.
The validation record in `README.md` distinguishes compilation, font
embedding, complete page rendering, contact-sheet review, and full-resolution
inspection. PDFs retained beneath `assets/` are research figures, not
manuscripts.

The live source now postdates that receipt. Its 14,201-line, 663,950-byte TeX
source has SHA-256
`fe19f8a028a7310d4604a3ab78db5325b58df3d0004dbe1922acb5cdec8928fb`.
It incorporates exhaustive crosswalks for `QPochhammerEntire` (zero
definitions and five theorems), `QPochhammerInfinite` (one definition and
twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), and `GaussianBinomialPalindromic` (zero definitions and twelve
theorems). The `QPochhammerEntire.lean` leaf proves the fixed-nome
single-symbol locally uniform product and differentiability, the
division-free factor-zero criterion including `q = 0`, the reciprocal-power
zero lattice for nonzero nome, and simple analytic order at every zero. The
forward status inventory is 70 exact / 82 partial / 122 none / 8 interface;
the original 191-result pre-Fabius core is 36 / 29 / 123 / 3 and the
q-integer/Gaussian chapter is 8 / 0 / 1 / 0. The five-publication concordance
has 65 Lean-proved, 413 human-proved frontier, 60 not-applicable, and 9
conjecture rows.
No normal-convergence claim is made for the additional outer product indexed
by spectral scale. No PDF was generated for this source-only update, so the
retained 347-page artifact is historical and must not be treated as rendering
the current source.

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
17-file delivery matched the archive hash already recorded above.  No checksum
ledger was submitted: the repository-generated arrival ledger verified all 17
payloads before normalization.  Twelve hashes agree with the pinned source
ledger, while five CSV hashes differ solely because the arrival ledger records
their pre-normalization line endings.  A later normalized edition passed three
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
seven-file normalized ledger, exact replay of the retained 44-line numerical
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
checksum ledgers, six generated report PDFs, twenty generated figures, and
nineteen generated data or audit files.  Four additional untracked files in
the forward-expansion package are ordinary `.aux`, `.log`, `.out`, and `.toc`
build intermediates.

Every entry in all six source checksum ledgers matched its corresponding file
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
the one disclosed last-digit runtime drift, while `assets/SHA256SUMS` fixes
the post-migration bytes.

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
