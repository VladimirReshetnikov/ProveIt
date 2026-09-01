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
| `Inverse_and_Sampling_Frontiers/` | `Inverse_and_Sampling_Frontiers.tex` | 6,603 | `3bae6a0d6df38778f31365acb8d5da7a09bd3ecafcd2a257c6be964df3740601` | Inverse-dyadic germs, finite-prefix inversion, Barnes--Rvachev deconvolution, self-sampling, alias filtration, Richardson acceleration, and inverse-moment Appell theory. |
| `Inverse_Endpoint_All_Orders/` | `Inverse_Endpoint_All_Orders.tex` | 1,978 | `1dbf538e16b619f2c03403333cd46c912dc28b66a2823a1bb1f2b81ba859613e` | All-orders endpoint inversion, Lambert/Wright-omega carriers, Bell-polynomial coefficient extraction, derivative hierarchy, exact dyadic completion, and transseries frontiers. |
| `Inverse_Fabius_Computability_Report/` | `inverse_fabius_computability.tex` | 2,937 | `a6932249804ea3fb07a08b09542e123bbbca23b76a29e13ef27c91aa902ffbe3` | Exact inverse moduli, effective uniform continuity, certified tolerant bisection, sequential computability, and complexity consequences. |

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
two superseded source subgroups. The deduplicated canonical asset tree contains
63 live payloads, exhaustively listed by
[`assets/SHA256SUMS`](assets/SHA256SUMS).

Arrival ledgers and internal source hashes remain under
[`assets/provenance/`](assets/provenance/), including separate records for the
sampling, endpoint, computability, non-elementarity, and inverse-iterate
lineages. The five historical source PDFs are retired with their source
layouts after the canonical publication passes; their bytes remain recoverable
from the pre-retirement revision. Unique scripts, exact tables, data, figures,
captured outputs, requirements, and audit material were migrated or explicitly
dispositioned. No numerical output is used as a premise of a theorem.

## Canonical publication artifact

On 1 September 2026, exactly three serial `pdflatex` passes over the canonical
TeX at revision `1c032f51ce0d401f8d311d14fdb09b12540a0c80` produced
`inverse_fabius_theory.pdf`. The synchronized artifact has 133 A4 pages,
contains 2,414,428 bytes, and has SHA-256
`1d9cf53c16d50e8419eadd746820d358f7f917867a592eb170ad5b326101d163`.
Its final-pass log contains no TeX error, LaTeX or package warning, overfull or
underfull box, undefined-reference notice, or rerun request.

All 31 font rows are embedded and subset Type 1 fonts; Libertinus is present
and Type 3 is absent. The PDF has populated title, subject, keywords, and
author metadata. Every one of its 133 pages was rendered at 120 dpi and
inspected as part of the complete nine-sheet visual review. Text extraction
covered all 133 pages without an unexpectedly blank page.

## Editorial relationship

The five inputs were peer sources, not successive editions. They overlapped in
normalization, nowhere analyticity, inverse regularity, endpoint inversion,
Lambert coordinates, Bell-polynomial reversion, self-sampling, and Lean status,
while each also contributed unique results. The canonical volume therefore
uses a neutral title, states common mathematics once, and records semantic
provenance result by result rather than selecting one input wholesale.
