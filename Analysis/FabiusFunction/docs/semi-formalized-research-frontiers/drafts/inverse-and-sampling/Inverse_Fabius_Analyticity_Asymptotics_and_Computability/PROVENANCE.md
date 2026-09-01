# Provenance ledger

The canonical volume consolidates five peer inputs at repository revision
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.  That revision is stored in
`audit/SOURCE_REVISION` and remains the immutable source for the result
extractor even after the superseded layouts are retired.

| Source package | Main source at the pin | Lines | SHA-256 | Principal role |
| --- | --- | ---: | --- | --- |
| `Non_Elementarity_of_the_Fabius_Function/` | `Non_Elementarity_of_the_Fabius_Function.tex` | 1,057 | `8021f1f3aba753aac67a9a2b6ccbb7e2487ee1d3f60a8df3fd33551c0504c737` | Dense-open analyticity of elementary expressions and algebraic/inverse branch extensions; local non-elementarity of the Fabius function and its inverse. |
| `inverse_fabius_iterates_nowhere_analytic/` | `inverse_fabius_iterates_nowhere_analytic.tex` | 1,742 | `eda8c676e00a68c1e57e36ee22bfb3502cd56dd95f5630efcaf6a7f0f3b3d3d5` | Nowhere analyticity and formal Taylor-radius behavior of positive inverse iterates, forward spine estimates, formal reversion, endpoint Holder obstructions, and iterated endpoint scales. |
| `Inverse_and_Sampling_Frontiers/` | `Inverse_and_Sampling_Frontiers.tex` | 6,603 | `3bae6a0d6df38778f31365acb8d5da7a09bd3ecafcd2a257c6be964df3740601` | Inverse-dyadic germs, finite-prefix inversion, Barnes--Rvachev deconvolution, self-sampling, alias filtration, Richardson acceleration, and inverse-moment Appell theory. |
| `Inverse_Endpoint_All_Orders/` | `Inverse_Endpoint_All_Orders.tex` | 1,978 | `1dbf538e16b619f2c03403333cd46c912dc28b66a2823a1bb1f2b81ba859613e` | All-orders endpoint inversion, Lambert/Wright-omega carriers, Bell-polynomial coefficient extraction, derivative hierarchy, exact dyadic completion, and transseries frontiers. |
| `Inverse_Fabius_Computability_Report/` | `inverse_fabius_computability.tex` | 2,937 | `a6932249804ea3fb07a08b09542e123bbbca23b76a29e13ef27c91aa902ffbe3` | Exact inverse moduli, effective uniform continuity, certified tolerant bisection, sequential computability, and complexity consequences. |

The inverse-and-sampling source is itself the editorial consolidation of three
earlier reports; the all-orders source consolidates three independent endpoint
asymptotics packages; the computability source arrived as a single five-file
package.  The inverse-iterate source is a derived companion to a forward
iterate report elsewhere in the corpus and carries reproducible numerical
assets.  Their internal provenance ledgers and archived source hashes are
retained in the canonical asset tree and its nested integrity ledger.  Git
history remains the byte-level archive for material that is deliberately not
migrated.

The five inputs are not successive editions.  They overlap in normalization,
nowhere analyticity, inverse regularity, endpoint inversion, Lambert
coordinates, Bell-polynomial reversion, and Lean status, but each also contains
unique results.  The canonical volume therefore uses a neutral title and
records semantic provenance result by result instead of choosing one input
wholesale.

## Canonical publication artifact

The validated publication pair is `inverse_fabius_theory.tex` and
`inverse_fabius_theory.pdf`.  The final source contains 296 lines and 11,625
bytes and has SHA-256
`7b8cea5ff685db3bb676e08f8e3b3c6586a7702f8bf3a85298fb9ced00054d25`.
Its exhaustive 23-input closure has SHA-256
`0c856dd3329d53e2155616dfff8f9e503bd6a0f449622f0eae4e9cc84b548ee4`.
That closure comprises the master, the shared repository notation file, all
nine canonical chapter files, three generated TeX fragments, and nine
publication PNG figures.

The matching final PDF has 134 A4 pages and 2,027,726 bytes, with SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
Exactly three guarded final-source pdfLaTeX passes returned zero and produced
127, 134, and 134 pages.  The input closure remained unchanged before and
after every pass, with no TeX/Lean/Lake interleave.  The detailed log, text,
page-box, font, fresh visual, and package-cleanliness results are recorded in
`VALIDATION.md`.  Root `SHA256SUMS` is the exhaustive current package ledger;
it includes `assets/SHA256SUMS` as a permanent payload while leaving that
independently useful nested asset ledger unchanged.

Publication validation changes no historical claim, source pin, concordance
row, disposition, asset lineage, or arrival checksum recorded above.  It
certifies only that the stated final PDF is the reviewed rendering of the
exact source closure identified here.
