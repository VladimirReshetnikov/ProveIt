# Provenance ledger

## Immutable source snapshot

The canonical volume was extracted from five peer inputs at repository revision
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`. That exact revision is stored in
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION) and remains the immutable
source for the 194-row result extractor and the 88-row source-asset audit.
Later notation normalization in the live packages did not change this
extraction pin.

## Immediate inputs

| Source package | Main source at the pin | Lines | SHA-256 | Principal role |
| --- | --- | ---: | --- | --- |
| `Non_Elementarity_of_the_Fabius_Function/` | `Non_Elementarity_of_the_Fabius_Function.tex` | 1,057 | `8021f1f3aba753aac67a9a2b6ccbb7e2487ee1d3f60a8df3fd33551c0504c737` | Dense-open analyticity of elementary expressions and algebraic/inverse branch extensions; local non-elementarity of the Fabius function and its inverse. |
| `inverse_fabius_iterates_nowhere_analytic/` | `inverse_fabius_iterates_nowhere_analytic.tex` | 1,742 | `eda8c676e00a68c1e57e36ee22bfb3502cd56dd95f5630efcaf6a7f0f3b3d3d5` | Nowhere analyticity and formal Taylor-radius behavior of positive inverse iterates, forward spine estimates, formal reversion, endpoint Holder obstructions, and iterated endpoint scales. |
| `Inverse_and_Sampling_Frontiers/` | `Inverse_and_Sampling_Frontiers.tex` | 6,607 | `d5f5ba096af58634fe0693bd4731b10898a85ad38204c661edde2ddbe38ed04a` | Inverse-dyadic germs, finite-prefix inversion, Barnes--Rvachev deconvolution, self-sampling, alias filtration, Richardson acceleration, and inverse-moment Appell theory. |
| `Inverse_Endpoint_All_Orders/` | `Inverse_Endpoint_All_Orders.tex` | 1,979 | `0709a513017d42b94f931f6e4a2b0ac396464497c8fa75ef660545f4ab163507` | All-orders endpoint inversion, Lambert/Wright-omega carriers, Bell-polynomial coefficient extraction, derivative hierarchy, exact dyadic completion, and transseries frontiers. |
| `Inverse_Fabius_Computability_Report/` | `inverse_fabius_computability.tex` | 2,937 | `d161226599c27c3a7b7818bcf9d30c226be66fdf2f46d359735d4f95f5044ae6` | Exact inverse moduli, effective uniform continuity, certified tolerant bisection, sequential computability, and complexity consequences. |

## Historical directory lineage

Relative to
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/`,
the five immediate source layouts were:

- `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`;
- `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`;
- `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`;
- `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`;
- `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`.

They remain recoverable together at
`93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
snapshot. Git history is the byte-level archive; these strings are deliberately
retained as historical locators and must not be rewritten as if the old
directories were still live.

The immediate inputs also carry earlier lineage:

- `Inverse_and_Sampling_Frontiers/` had consolidated
  `Fabius_Inverse_Frontier_Report_Source_and_PDF/`,
  `fabius_frontier_dyadic_inverse_barnes_report/`, and
  `Fabius_Dyadic_Self_Sampling_Frontier_Package/`;
- `Inverse_Endpoint_All_Orders/` had consolidated
  `inverse_fabius_all_orders_package/`,
  `inverse_fabius_asymptotics_report/`, and
  `inverse_fabius_asymptotics_package/`;
- `Non_Elementarity_of_the_Fabius_Function/` was reclassified from the former
  top-level `Analysis/FabiusFunction/docs/Non_Elementarity_of_the_Fabius_Function/`
  pair; an older, byte-distinct first edition remains under
  `docs/archive/standalone-studies/`;
- `Inverse_Fabius_Computability_Report/` arrived through
  `drafts/incoming/Inverse_Fabius_Computability_Report.zip`, outer SHA-256
  `755d77354490d25d4f327419d0345623e91ea49dd4ba681ba97c84a0b686b8c1`;
- `inverse_fabius_iterates_nowhere_analytic/` arrived through
  `drafts/incoming/inverse_fabius_iterates_nowhere_analytic.zip`, outer
  SHA-256
  `8b1c05d59e120ecd20d69cd5aeb0009639f2f3b9a6c9fef32bdf82270eee16bd`.

## Result and asset disposition

[`theorem_concordance.csv`](theorem_concordance.csv) records the semantic
disposition of every immutable source result.
[`ASSET_DISPOSITION.csv`](ASSET_DISPOSITION.csv) records the SHA-256, size,
semantic class, canonical destination, and disposition of all 88 files in the
two superseded source subgroups. The former 63-payload asset checkpoint
included eight historical ledger payloads; after their retirement, the
deduplicated canonical asset tree contains 55 live files. Their source and
destination digests remain recorded in the disposition table and Git history.

Three non-checksum provenance files remain under
[`assets/provenance/`](assets/provenance/): the endpoint corpus audit, the
inverse-iterate `MANIFEST.txt`, and the inverse-iterate repository audit.
Retired arrival-ledger and internal-source-hash bytes for all five lineages
remain identified by `ASSET_DISPOSITION.csv` and recoverable from the pinned
Git revision. The five historical source PDFs were retired with their source
layouts only after the canonical publication gate passed; their bytes remain
recoverable from the pre-retirement revision. Unique scripts, exact tables,
data, figures, captured outputs, requirements, and audit material were migrated
or explicitly dispositioned. No numerical output is used as a premise of a
theorem.

## Canonical source and synchronized publication artifact

The current canonical master `inverse_fabius_theory.tex` has 293 lines and
11,514 bytes and SHA-256
`92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c`.
Its independently measured `b899` recursive TeX closure has 17 files, 10,682
lines, and 431,748 bytes, with digest
`6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e`.

Exactly three serial halt-on-error passes from absent sidecars ran 132 pages /
1,983,313 bytes → 137 / 2,045,485 → 137 / 2,045,486. The synchronized PDF
has 137 A4 pages and 2,045,486 bytes, with SHA-256
`cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995`.
All log, reference/rerun, metadata, all-page A4/rotation/render/text, font, visual,
cleanup, and forbidden-basename gates passed; all 31 font rows are embedded and
subset, six are Libertinus, none is Type 3, and the only box diagnostics are
two nonblocking horizontal boxes of 2.42 and 2.45 pt.

The purpose-specific 23-input `SOURCE_CLOSURE.sha256` file has SHA-256
`aedf007c2cd150b1f83de6d8996b4bf31e267b3dbcec2d5cd4720f5d92122bdb`.
It comprises the master, shared notation, all nine chapters, three generated
TeX fragments, and nine publication figures at its named pre-overlay
checkpoint. It was intentionally not regenerated for `b899` and is historical,
not the current closure receipt. The prior PDF has 134 A4 pages and 2,027,726
bytes, with SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`;
its historical passes produced 127 → 134 → 134 pages. Detailed evidence for
both current and historical receipts is recorded in `VALIDATION.md`.
The former root and nested asset checksum ledgers are retired and recoverable
from Git; publication validation changes no historical claim, concordance row,
disposition, lineage, or arrival checksum recorded above.

## Editorial relationship

The five inputs were peer sources, not successive editions. They overlapped in
normalization, nowhere analyticity, inverse regularity, endpoint inversion,
Lambert coordinates, Bell-polynomial reversion, self-sampling, and Lean status,
while each also contributed unique results. The canonical volume therefore
uses a neutral title, states common mathematics once, and records semantic
provenance result by result rather than selecting one input wholesale.
