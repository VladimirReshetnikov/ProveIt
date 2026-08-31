# Inverse Fabius analyticity, asymptotics, computability, and sampling

This directory is the canonical consolidation workspace for five overlapping
volumes currently stored in the two source subgroups beside it:

- `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`;
- `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`;
- `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`;
- `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`;
- `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`.

The finished deliverable will be one LaTeX/PDF volume covering nowhere
analyticity, non-elementarity, inverse iterates, inverse-dyadic germs, endpoint
asymptotics, dyadic self-sampling, exact inverse moduli, and certified
computation.  Shared definitions and proofs will occur once; specialized
consequences will point back to the strongest common statement.

Status language is strict:

- `Lean-proved` requires an exact compiled declaration with matching
  hypotheses and conclusion.
- `Human-proved frontier result` requires a complete proof in the canonical
  volume but need not yet have an exact Lean counterpart.
- `Conjecture` or `open problem` means that a genuine proof obligation
  remains.

`theorem_concordance.csv` will record the disposition of every source result
environment.  `PROVENANCE.md` records source and asset lineage, while
`audit/SOURCE_REVISION` pins the immutable pre-consolidation tree used by the
reproducible extractor.

The five source packages remain live during review.  They will be removed
only after every result and unique reproducibility asset has a canonical
disposition and the matching canonical PDF has passed the publication gate.
