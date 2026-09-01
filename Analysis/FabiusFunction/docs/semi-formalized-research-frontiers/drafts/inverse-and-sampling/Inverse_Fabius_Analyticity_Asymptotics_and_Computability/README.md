# Inverse Fabius Theory: analyticity, asymptotics, computability, and dyadic sampling

This directory is the canonical source and publication package for
[`inverse_fabius_theory.tex`](inverse_fabius_theory.tex)
([PDF](inverse_fabius_theory.pdf)). It replaces five overlapping reports on
inverse Fabius theory and the Rvachev law: dense-open analyticity and
non-elementarity, positive inverse iterates, inverse-dyadic germs,
Barnes--Rvachev deconvolution, all-orders Lambert--W endpoint inversion,
dyadic self-sampling and Richardson filters, exact inverse moduli, and
certified computation.

Every nonconjectural retained assertion has a complete human-readable proof.
`Lean-proved` is reserved for an exact current declaration with matching
hypotheses and conclusion; other complete proofs are labelled
`human-proved frontier result`. Genuine unresolved obligations remain visibly
labelled as conjectures or open problems, and numerical experiments are used
only as reproducible checks.

The package audit surfaces are:

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

The three newest exact source-row matches are centered Appell deconvolution,
positive-degree Appell mean-zero, and arbitrary-phase polynomial
deconvolution. The Appell lattice theorem remains human-proved: Lean covers
its arbitrary-phase `0 <= n <= N` formula, but not its additional degree-`N+1`
clause at the parity-selected superconvergent phases.

## Publication certification

The synchronized publication artifact was built from the canonical TeX after
merging `origin/main` through `c3720b763d159c3a009b66e6e89ac500b7843e98`
on 1 September 2026 in
exactly three serial `pdflatex` passes. The final-pass log contains no TeX
error, LaTeX or package warning, overfull or underfull box,
undefined-reference notice, or rerun request. The resulting unencrypted PDF
has 133 A4 pages and 2,417,414 bytes; its SHA-256 is
`83a2cc2050e4f6c0c6ea26b472c09f05d4c77d2d84d4ba47e316d8176e7c11c6`.

Every one of its 31 font rows is Type 1, embedded, and subset; Libertinus is
present and no Type 3 font occurs. All 133 pages were rendered at 120 dpi and
inspected in the complete nine-sheet contact set. Text extraction covered all
133 pages without an unexpectedly blank page, and the title, subject,
keywords, and author metadata are populated.
