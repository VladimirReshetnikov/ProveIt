# Novelty exclusion audit

Reviewed source commit: `e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11`.

Exclusion audit of current incoming simplification ZIP and earlier retired packet explicitly linked by incoming README. Reports and supplementary source notes read in full; prototype declaration lists inventoried. Historical mathematical construction packets are not claimed to have been exhaustively read.

## Reviewed sources

- **A:** `docs/incoming/diophantine-lean-simplification-2026-10-26.zip`, member `report.tex` (920 lines).
- **B:** `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex` (442 lines), the retired packet linked explicitly by `docs/incoming/README.md` lines 14-18.
- **B-digits:** that packet's `source_notes/digits-review.md`; its checker/circuit supplementary notes were also reviewed.

**Important:** B-digits contains proposals beyond the main report, especially origin decrement, direct physical sums, and coherent source-window extraction. These count as already proposed.

## Exclusion catalog

| ID | Already proposed technique | Precise evidence |
|---|---|---|
| E01 | Core list lookup/membership lemmas | A:173-218; B:132-143 |
| E02 | Recursor congruence instead of repeated induction | B:114-131 |
| E03 | Assignment naturality under Sum.map and renaming | A:219-268; B:144-161 |
| E04 | Splitting concatenated witness blocks with Fin.addCases | A:241-268 |
| E05 | Move constructor projection/count lemmas to earlier modules | A:269-283 |
| E06 | Generic validated-history fold and Produces append/step laws | A:286-326 |
| E07 | Generic scanner fixed-state, successor, invariant, and encoded-list simulations | A:327-361; B:280-295 |
| E08 | Dynamic-seed and parameterized primitive-recursive iterateFrom | A:362-379 |
| E09 | Shared tag dispatch and exact numeric Boolean reflection | A:380-396; B:296-310 |
| E10 | Sum-of-squares zero criterion, shared evaluation, degree and cost | A:399-442; B:162-189 |
| E11 | Generic semiring gate specialization after data/semantics import split | A:443-468 |
| E12 | Move structural degree API early; specialize weighted degree to weight one | A:459-468; B:266-271 |
| E13 | Reuse exponent-label power certificates for generated circuit chains | A:483-523; B:192-210 |
| E14 | On-demand circuit node equation specialization and compact wrappers | A:524-545; B:211-239 |
| E15 | Shared topological circuit induction for indexed invariants | B:240-255 |
| E16 | Commutative operand-swap relation and common circuit translation skeleton | B:258-265 |
| E17 | Generic append topology/predicate/evaluation invariants | B:272-277 |
| E18 | Exact half-radix quotient/remainder identity replaces finite cases | A:548-581; B:319-329 |
| E19 | Physical field residue, source-offset and off-origin mask normal forms | A:582-616; B-digits:167-204 |
| E20 | Project stronger coefficient congruence to weaker moduli | A:605-611; B:313-318 |
| E21 | Decode and reuse Pell/source-register arithmetic equations | A:617-641 |
| E22 | Exact carry decomposition API; derive recurrence/residue/reset | A:644-677; B:343-354 |
| E23 | Generic finite chunk dispatcher and balanced partial-sum assembly | A:678-711 |
| E24 | Shared copied-field bounds and descriptor interface | A:712-725 |
| E25 | Conditional padding witness only within relevant phase branch | B:330-342 |
| E26 | Generic no-borrow origin decrement for packed words | B-digits:205-229 |
| E27 | Expose selectorCount physical finite-sum identity directly | B-digits:230-248 |
| E28 | Share restored canonical window extraction with coherent witnesses | B:353-354; B-digits:249-268 |
| E29 | Definability-aware omega induction transport | B:357-364 |
| E30 | Arbitrary-model extraction and sealed completeness bridge | A:728-767; B:365-372 |
| E31 | Arity-generic closed-formula satisfaction transport | A:768-781 |
| E32 | Scoped simp boundaries, dependency placement, certificate granularity and profiling | A:782-840; B:373-394 |

## Novelty standard

An idea is not fresh merely because a previously proposed helper is renamed, specialized to another existing client, or accompanied by a new proof. A fresh proposal must remove a different proof obligation, exploit a different mathematical invariant, or cover a materially different semantic boundary.

## Audit boundary

The absence of a phrase from the two reports is not a global novelty theorem. The intended claim is a source-grounded distinction from the two existing simplification packets at the pinned snapshot. Current maintained source must still be checked for an already implemented equivalent interface.

Incoming README and prior PLACEMENT.md link ADOPTION.md, but that path is absent at the reviewed commit. This audit makes no blanket adoption assertion.

Historical K215 proof-simplification archives linked much later in the incoming index concern a different subsystem. The 195 earlier Con(ZFC)-Diophantine construction reports are cross-referenced by the index, but they were not exhaustively inspected in this audit; avoid claiming exhaustive novelty against that entire research history.
