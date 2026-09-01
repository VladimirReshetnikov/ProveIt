# Inverse Fabius Theory: analyticity, asymptotics, computability, and dyadic sampling

This directory is the canonical consolidation and validated publication
package for five overlapping source volumes:

Every nonconjectural retained assertion has a complete human-readable proof.
`Lean-proved` is reserved for an exact current declaration with matching
hypotheses and conclusion; other complete proofs are labelled
`human-proved frontier result`. Genuine unresolved obligations remain visibly
labelled as conjectures or open problems, and numerical experiments are used
only as reproducible checks.

The canonical deliverable is one LaTeX/PDF volume covering nowhere
analyticity, non-elementarity, inverse iterates, inverse-dyadic germs, endpoint
asymptotics, dyadic self-sampling, exact inverse moduli, and certified
computation.  Shared definitions and proofs will occur once; specialized
consequences will point back to the strongest common statement.

- [`theorem_concordance.csv`](theorem_concordance.csv): all 194 immutable
  source-result rows, fully dispositioned as 39 Lean-proved, 106 human-proved
  frontier results, 10 conjectures, 15 open problems, and 24 non-applicable
  source environments;
- [`LEAN_CROSSWALK.md`](LEAN_CROSSWALK.md): exact module and declaration
  matches, formalization boundaries, and five separately classified
  post-snapshot additions;
- [`ASSET_DISPOSITION.csv`](ASSET_DISPOSITION.csv): the disposition of all 88
  files in the two superseded source subgroups;
- [`assets/SHA256SUMS`](assets/SHA256SUMS): the exhaustive live ledger for 63
  retained, deduplicated reproducibility payloads;
- [`PROVENANCE.md`](PROVENANCE.md): source hashes, arrival lineage, nested
  predecessors, and immutable recovery points.

The result and asset extractors are pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION) to
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.
The five later notation-normalized source layouts remain recoverable together
at `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
repository snapshot. The old paths are retained as provenance locators, not
as live links.

`theorem_concordance.csv` records the disposition of all 194 source-result
environments while preserving the ten immutable source fields reproduced from
`audit/SOURCE_REVISION`.  Its current totals are 47 Lean-proved, 98
human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows.  Eight inverse-computability rows now have exact compiled
counterparts: the main theorem, the three tolerant-difference branch
certificates, tolerant-bisection correctness, unit-interval sequential
inversion, computable clamping, and sequential computability of the totalized
inverse.  The abstract inversion theorem remains human-proved because the
generic Lean theorem assumes a computable reciprocal inverse modulus rather
than deriving that modulus and effective continuity from a computable positive
gap sequence.  The centered Appell deconvolution, positive-degree Appell
mean-zero, and arbitrarily phased polynomial-deconvolution rows also have exact
named Lean counterparts.  The Appell lattice theorem remains human-proved:
Lean covers its arbitrary-phase `0 <= n <= N` formula, but not its additional
degree-`N+1` clause at the parity-selected superconvergent phases.  The static
canonical validator passes.  `PROVENANCE.md` records source and asset lineage.

## Validated publication

The canonical publication pair is now final:

- `inverse_fabius_theory.tex`: 296 lines, 11,625 bytes, SHA-256
  `7b8cea5ff685db3bb676e08f8e3b3c6586a7702f8bf3a85298fb9ced00054d25`;
- its exhaustive 23-input source closure: SHA-256
  `0c856dd3329d53e2155616dfff8f9e503bd6a0f449622f0eae4e9cc84b548ee4`;
- `inverse_fabius_theory.pdf`: 134 A4 pages, 2,027,726 bytes, SHA-256
  `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.

Exactly three guarded final-source pdfLaTeX passes returned zero and produced
page counts 127, 134, and 134.  The 23-input closure was unchanged before and
after every pass, with no TeX/Lean/Lake interleave.  The final log has zero
fatal, undefined, multiply-defined, duplicate, actionable-rerun, or overfull
diagnostics; all-page text, geometry, page-box, font, and fresh targeted visual
checks pass.
`VALIDATION.md` is the detailed publication receipt.  The exhaustive root
`SHA256SUMS` covers every permanent package file except itself, including the
independent nested `assets/SHA256SUMS` ledger.

The publication gate is therefore complete.  The five source packages and
their retained renderings are historical inputs represented by the immutable
revision, concordance, migrated evidence, and repository history; they are not
parallel renderings of this canonical master.
