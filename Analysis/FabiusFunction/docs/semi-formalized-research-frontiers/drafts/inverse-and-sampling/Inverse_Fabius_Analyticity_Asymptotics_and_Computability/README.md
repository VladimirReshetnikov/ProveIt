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

`theorem_concordance.csv` records the disposition of all 194 source-result
environments while preserving the ten immutable source fields reproduced from
`audit/SOURCE_REVISION`.  Its current totals are 39 Lean-proved, 106
human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows.  The centered Appell deconvolution, positive-degree Appell
mean-zero, and arbitrarily phased polynomial-deconvolution rows now have exact
named Lean counterparts.  The Appell lattice theorem remains human-proved:
Lean covers its arbitrary-phase `0 <= n <= N` formula, but not its additional
degree-`N+1` clause at the parity-selected superconvergent phases.  The static
canonical validator passes.  `PROVENANCE.md` records source and asset lineage.

The canonical PDF is still absent, so the publication gate is not complete.
The five source packages remain live until that matching artifact has passed
the gate; their retained PDFs remain historical/source artifacts rather than
a rendering of this canonical master.
