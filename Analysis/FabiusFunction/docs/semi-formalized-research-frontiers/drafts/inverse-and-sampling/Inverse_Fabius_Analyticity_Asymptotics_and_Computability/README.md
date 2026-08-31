# Inverse Fabius analyticity, asymptotics, computability, and sampling

This directory contains the canonical-source draft for five overlapping
volumes stored in the two source subgroups beside it:

- `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`;
- `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`;
- `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`;
- `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`;
- `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`.

`inverse_fabius_theory.tex` and its nine input chapters now form one LaTeX
source covering nowhere analyticity, non-elementarity, inverse iterates,
inverse-dyadic germs, endpoint asymptotics, dyadic self-sampling, exact inverse
moduli, and certified computation. Shared definitions and proofs occur once;
specialized consequences point back to the strongest common statement.

## Current package state

- `audit/SOURCE_REVISION` pins the immutable pre-consolidation tree at
  `0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.
- `audit/source_result_inventory.csv` is the reproducible 194-row raw
  extraction from that pin. Its canonical disposition fields are blank: it is
  source evidence, not a reviewed theorem concordance.
- `ASSET_DISPOSITION.csv` accounts for all 88 files in the two source
  subgroups. The deduplicated retained payloads live under `assets/`, and the
  exhaustive `assets/SHA256SUMS` ledger verifies all 61 payload rows.
- `PROVENANCE.md` and `assets/provenance/` retain source and checksum lineage;
  historical PDFs and figure PDFs in the source/asset record are not a render
  of the canonical master.

`theorem_concordance.csv` does not yet exist. The static source validator
requires that reviewed 194-row file and currently stops at its absence. There
is also no canonical `inverse_fabius_theory.pdf`; no TeX build, rendered-page
inspection, or publication gate is claimed for this source draft.

Status language is strict:

- `Lean-proved` requires an exact compiled declaration with matching
  hypotheses and conclusion.
- `Human-proved frontier result` requires a complete proof in the canonical
  volume but need not yet have an exact Lean counterpart.
- `Conjecture` or `open problem` means that a genuine proof obligation
  remains.

The pending `theorem_concordance.csv` must record the reviewed disposition of
every source result environment and map retained assertions to canonical
labels and exact Lean declarations where applicable.

The five source packages remain live during review. They will be removed only
after every result has a reviewed canonical disposition, every unique asset
remains accounted for, and the matching canonical PDF has passed the full
publication gate.
