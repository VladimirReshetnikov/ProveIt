# Provenance ledger

The canonical volume consolidates five peer inputs at repository revision
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.  That revision is stored in
`audit/SOURCE_REVISION` and remains the immutable source for the result
extractor even after the superseded layouts are retired.

| Source package | Main source at the pin | Lines | SHA-256 | Principal role |
| --- | --- | ---: | --- | --- |
| `Non_Elementarity_of_the_Fabius_Function/` | `Non_Elementarity_of_the_Fabius_Function.tex` | 1,057 | `8021f1f3aba753aac67a9a2b6ccbb7e2487ee1d3f60a8df3fd33551c0504c737` | Dense-open analyticity of elementary expressions and algebraic/inverse branch extensions; local non-elementarity of the Fabius function and its inverse. |
| `inverse_fabius_iterates_nowhere_analytic/` | `inverse_fabius_iterates_nowhere_analytic.tex` | 1,742 | `eda8c676e00a68c1e57e36ee22bfb3502cd56dd95f5630efcaf6a7f0f3b3d3d5` | Nowhere analyticity and formal Taylor-radius behavior of positive inverse iterates, forward spine estimates, formal reversion, endpoint Holder obstructions, and iterated endpoint scales. |
| `Inverse_and_Sampling_Frontiers/` | `Inverse_and_Sampling_Frontiers.tex` | 6,607 | `d5f5ba096af58634fe0693bd4731b10898a85ad38204c661edde2ddbe38ed04a` | Inverse-dyadic germs, finite-prefix inversion, Barnes--Rvachev deconvolution, self-sampling, alias filtration, Richardson acceleration, and inverse-moment Appell theory. |
| `Inverse_Endpoint_All_Orders/` | `Inverse_Endpoint_All_Orders.tex` | 1,979 | `0709a513017d42b94f931f6e4a2b0ac396464497c8fa75ef660545f4ab163507` | All-orders endpoint inversion, Lambert/Wright-omega carriers, Bell-polynomial coefficient extraction, derivative hierarchy, exact dyadic completion, and transseries frontiers. |
| `Inverse_Fabius_Computability_Report/` | `inverse_fabius_computability.tex` | 2,937 | `d161226599c27c3a7b7818bcf9d30c226be66fdf2f46d359735d4f95f5044ae6` | Exact inverse moduli, effective uniform continuity, certified tolerant bisection, sequential computability, and complexity consequences. |

The inverse-and-sampling source is itself the editorial consolidation of three
earlier reports; the all-orders source consolidates three independent endpoint
asymptotics packages; the computability source arrived as a single five-file
package.  The inverse-iterate source is a derived companion to a forward
iterate report elsewhere in the corpus and carries reproducible numerical
assets. Their internal provenance ledgers and archived source hashes are now
retained under `assets/provenance/`; unique data, scripts, generated fragments,
and figures are organized by mathematical role under `assets/`.
`ASSET_DISPOSITION.csv` accounts for all 88 files in the two source subgroups,
and the exhaustive live `assets/SHA256SUMS` ledger verifies all 61 retained
payloads. Git history remains the byte-level archive for material deliberately
not migrated.

The five inputs are not successive editions.  They overlap in normalization,
nowhere analyticity, inverse regularity, endpoint inversion, Lambert
coordinates, Bell-polynomial reversion, and Lean status, but each also contains
unique results.  The canonical volume therefore uses a neutral title and
records semantic provenance result by result instead of choosing one input
wholesale.

The canonical master and nine chapter sources now exist. The pinned
`audit/source_result_inventory.csv` reproduces 194 raw source-result rows, but
its canonical-disposition columns remain unreviewed and
`theorem_concordance.csv` is absent. Consequently the source validator cannot
complete. No canonical PDF has been built or inspected, and source-package
PDFs or PDFs retained as evidence must not be described as renderings of the
canonical master. All five source packages remain live until both the reviewed
result-disposition gate and the canonical PDF publication gate pass.
