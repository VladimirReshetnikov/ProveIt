# Repository and Literature Audit

## Snapshot

The report was prepared against the live `main` branch of
`VladimirReshetnikov/ProveIt` on 30 August 2026, focusing on
`Analysis/FabiusFunction/docs` and its descendants.

## Full-text nonduplication baseline

The two principal full-text sources were:

1. `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
   — 9,509 lines in the inspected snapshot.
2. `docs/semi-formalized-research-frontiers/semi-formalized-research-frontiers.tex`
   — 14,587 lines in the inspected snapshot.

The first is the canonical current exposition. The second explicitly consolidates and records the provenance of eleven former research notebooks, including work on exact dyadic formulas, q-connections, repeated integration, Thue–Morse convergence, inverse asymptotics, and small-argument saddle analysis. Repository paper-coverage, asymptotic-completion, and documentation audits were also used to distinguish formalized facts, semi-formal arguments, historical sources, and superseded copies.

Archived or superseded TeX variants were therefore checked through the repository’s own consolidation and provenance map rather than counted as independent mathematical contributions. This avoids both accidental duplication and the misleading appearance of broader coverage obtained merely by rereading copied material.

## Independent literature consulted

The report bibliography includes, among other sources:

- J. Arias de Reyna, *An infinitely differentiable function with compact support: Definition and properties*.
- J. Arias de Reyna, *Arithmetic of the Fabius function*.
- J. K. Haugland, exact Fabius-function evaluations.
- S. Have, odd moments of the Fabius function.
- C. Aistleitner, M. Hofer, and G. Larcher, parametric Thue–Morse products.
- L. Tóth, Thue–Morse Dirichlet series.
- A. Sebbar, connections among Viète products, the Fabius function, and partitions.
- Recent compactly supported kernel work using Rvachev/Fabius constructions.

## Novelty policy

Every proposed addition was compared against the canonical exposition, the consolidated frontier volume, and the relevant audit/provenance material. The report uses four status classes:

- **Proved here** — a complete proof or a reduction to a checked standard theorem is supplied.
- **Proof program** — the decisive algebraic or saddle structure is derived, but a technical uniformity or contour estimate remains.
- **Numerically supported** — deterministic reproducible evidence is supplied.
- **Conjectural** — a precise falsifiable statement is proposed.

The word “novel” is deliberately local: it means absent from the inspected repository snapshot. No assertion of global priority is made without a separate exhaustive literature review.

## Runtime limitation and mitigation

A direct `git clone` was unavailable in the execution runtime because outbound DNS for the container was blocked. Current GitHub raw-file and tree views were therefore read through the browsing interface. The canonical and consolidated TeX sources were available in full text, while repository provenance/audit documents were used to cover superseded lineages. This limitation is stated so that the source audit is reproducible and not overstated.

## Post-arrival repository audit

The repository intake was reviewed against the live formal corpus rather than
accepting the submitted novelty labels at face value. Existing Lean APIs
already cover the geometric-uniform series and probability law, its
positive-parameter distributional and density theory, convolution and
cumulant-tail formulas, finite sinc products, a general weighted analytic
sinc–zeta expansion, and the fixed dyadic half–quarter multisection. The
report now says so explicitly.

No current declaration was found that directly packages the submitted
negative-parameter affine duality, the closed all-parameter Bernoulli
cumulants, the Gaussian or large-deviation limits, the exact subdyadic
plateaux and derivative norms, the arbitrary-parameter zero divisor and
spectral zeta, the normalized moment-polynomial recurrence, the Legendre
scaling limit, or the arbitrary-parameter periodic Laplace phase. These
claims remain at the manuscript status stated by their local environments.
In particular, the Fourier-phase contour step has not been promoted to a
formal theorem. Filing this package therefore changes no formal coverage
ledger status.

The spectral and reciprocal-integer portions overlap the independently filed
Digital Spectral Geometry and Reciprocal-Integer Convolution Divisors
packages. An eight-gram comparison found no wholesale textual duplication;
the overlap is conceptual and is recorded in the report rather than hidden.

## Arrival preservation and normalized replay

The source archive `fabius_frontier_report_bundle-D.zip` was 1,508,514 bytes
with SHA-256
`39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`.
Its submitted 34-row checksum ledger was independently verified against all
archive members. That historical ledger remains recoverable byte-for-byte
from Git history.

The deterministic experiment suite was replayed in a clean Python 3.13
environment using the versions pinned in `requirements.txt`. Exact tables
reproduced exactly before the repository's LF normalization. The only
numerical differences from the submitted floating-point outputs were:

- four of 42 Edgeworth fields, maximum absolute drift
  `2.7755575615628914e-15`;
- 112 of 396 large-deviation fields, maximum absolute drift
  `5.572764472105973e-13`;
- 27 of 63 periodic-Fourier fields, maximum absolute drift
  `2.2455452587358634e-18`.

Seven of eight PNG previews were byte-identical. The remaining periodic
preview retained its dimensions, with 99.9629% of whole pixels identical and
mean absolute channel drift below `0.001`. The vector figures were
intentionally regenerated after requesting PDF font type 42, so their byte
changes are expected and remove the submitted Type-3 fonts.

## Repository normalization

The mathematical body was retained. The report now uses the shared
article/A4/27 mm/Libertinus preamble, with only report-local notation and
float settings after the common block. Generated CSVs use deterministic LF
line endings. A normalized-package ledger verified those bytes before
checksum ledgers were retired; it and the immutable arrival record remain
recoverable from Git history.
