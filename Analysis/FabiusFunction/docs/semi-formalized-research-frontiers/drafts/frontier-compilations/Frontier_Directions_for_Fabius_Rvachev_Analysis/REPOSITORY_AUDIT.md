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
