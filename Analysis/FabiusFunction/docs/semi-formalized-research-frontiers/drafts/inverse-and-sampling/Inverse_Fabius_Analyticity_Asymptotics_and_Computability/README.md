# Inverse Fabius analyticity, asymptotics, computability, and sampling

This directory is the canonical consolidation and validated publication
package for five overlapping source volumes:

- `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`;
- `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`;
- `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`;
- `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`;
- `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`.

The canonical deliverable is one LaTeX/PDF volume covering nowhere
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

## Validated publication

The canonical publication pair is now final:

- `inverse_fabius_theory.tex`: 296 lines, 11,625 bytes, SHA-256
  `7b8cea5ff685db3bb676e08f8e3b3c6586a7702f8bf3a85298fb9ced00054d25`;
- its exhaustive 23-input source closure: SHA-256
  `775c993b8e94c67b90e884e095daba7542140966863319206d8e6eb5fc23715b`;
- `inverse_fabius_theory.pdf`: 134 A4 pages, 2,027,672 bytes, SHA-256
  `a530b433392effd3a7941764c19b4c2dae3b35832ab569e9d6b630358646ede3`.

Exactly three guarded passes produced page counts 127, 134, and 134.  The
final log has zero fatal, undefined, actionable-rerun, duplicate, or overfull
diagnostics; text, page-box, font, and targeted visual checks all pass.
`VALIDATION.md` is the detailed publication receipt.  The exhaustive root
`SHA256SUMS` covers every permanent package file except itself, including the
independent nested `assets/SHA256SUMS` ledger.

The publication gate is therefore complete.  The five source packages and
their retained renderings are historical inputs represented by the immutable
revision, concordance, migrated evidence, and repository history; they are not
parallel renderings of this canonical master.
