# Source audit and provenance

Prepared 11 October 2026 (the user's local research date). This is a targeted continuation, not an exhaustive review of the repository or its incoming archive collection.

## Direct mathematical predecessors

### Affine Polarization of Gamma Normal Forms

Full TeX source retrieved from the user's Library:

`ProveIt_Affine_Gamma_Polarization_2026-10-11.tex`

SHA-256:

`36a06cf61ab08597c5526c3ced33af296fb536466974211073769ee41218c751`

Library file ID: `file_00000000cef081f59b0da75b3b53c5b0`, version 1. Size: 74,172 bytes.

The source's own metadata anchor is `92ee3aaf3087c0e0c29b9ed952e777de5d6accd0`. This is not presented as the revision of all live repository reads. The source's normal decomposition, centered Gamma representation, and affine square kernel are credited in the article. Its further-research question on arbitrary `u_2` powers multiplying `u_3^2`, and its higher-multiplicity coefficient question, motivated the present theorem.

The matching incoming archive was visible at the metadata level. Byte identity between the Library TeX and that archive's contents was **not** established. The Library source is the definite textual baseline for the claimed advance.

### Exact Harmonic-Tail Reconstruction and Variational Gamma Identities

Targeted connected-GitHub reads included:

- `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/harmonic-tail-gamma/article.tex`
- `.../sections/04_gamma_sectors.tex`
- `.../sections/02_gap_four.tex`

The article blob identity returned during inspection was `445e67f0cd60313113387d52d44d4ddc6eeaf244`. The existing all-`u_0,u_1,u_2` recurrence is recovered and replaced by a finite sum, not treated as an erroneous result. The general unequal-tail rank question is not solved by this work.

### Canonical manuscript and incoming notes

User-specified roots:

https://github.com/VladimirReshetnikov/ProveIt/tree/main/Analysis/Polylogarithms/docs/manuscript

https://github.com/VladimirReshetnikov/ProveIt/tree/main/docs/incoming

The canonical README, chapter metadata, and relevant normal-form material were inspected selectively. Incoming archive names and metadata were inspected, but the full incoming collection was not unpacked. Search results changed revisions during the session; the last additional search results carried `af91e74dfa841331c51e867542345a3643ee0bf0`. No assertion of a single complete frozen snapshot is made.

## Primary literature consulted

- Guo, Regensburger, Rosenkranz, *On Integro-Differential Algebras*, arXiv:1212.0266, especially §4.4.1. The author record gives JPAA 218 (2014), 456–471. https://arxiv.org/abs/1212.0266
- Espinosa–Moll, *On some Definite Integrals involving the Hurwitz Zeta function*, arXiv:math/0012078. https://arxiv.org/abs/math/0012078
- Espinosa–Moll, *On some integrals involving the Hurwitz zeta function: part 2*, arXiv:math/0107082. https://arxiv.org/abs/math/0107082
- NIST DLMF §5.15 (polygamma), §25.6 (integer zeta arguments), §25.11 (Hurwitz zeta), §25.12 (polylogarithms), §25.14 (Lerch). https://dlmf.nist.gov/

The normal-form complement and standard special-function calculus are not claimed as new. The new coefficient argument is polynomial-background transport plus highest-variation extraction. The analytic methods are classical applications to the resulting weights, with exact coefficient and endpoint normalizations supplied.

## Corrections established or proposed

The affine bibliography says `456--473` for Guo–Regensburger–Rosenkranz. Its page range should be `456--471`, as verified in the primary arXiv journal-reference record. The accompanying patch is generated against the inspected full TeX source and changes only that entry.

The canonical README blob `dc0fa26d0e5c2ede56df37c5640c7319681dfd25` duplicated the paragraph about the complete 1,032-input first-letter X family, rank 1,008, and kernel 24. The proposal is to remove the second copy if it remains in the integration target; no automatic patch against an uninspected later README is supplied.

No substantive mathematical error was established in the overlapping predecessor formulas. Common implementation pitfalls are documented as safeguards, not attributed as errors in the predecessors.

## Limitations

Targeted searches did not produce the universal coefficient formula, but this does not establish exhaustive historical priority. Parallel incoming work or intervening repository changes could overlap it. The final all-order proof should be independently reviewed before integration.

The exact checks are finite rational computations; the analytic diagnostics are floating point. Neither constitutes proof-assistant formalization, and the numerical residuals are not certified interval enclosures. The formal full-jet series is not asserted to converge after infinitely many analytic jet substitutions.
