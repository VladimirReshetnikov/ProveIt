# Source audit

Research date: 2026-10-06.

## Repository revision

The principal Section 5 reads were pinned to:

`869289aa38d59354e8dac2213df08ae0dd256415`

Repository: `VladimirReshetnikov/ProveIt`.

| Path under `Combinatorics/Ramsey/Lean/GowersSzemeredi/` | Inspected information | Blob SHA returned by the connector |
|---|---|---|
| `Section05.lean` | Corrected Lemma 5.2 target; Weyl parameters; square-root and partition thresholds | `882b17a01d76825b9dfd9679f00a93d5c0bf214c` |
| `Proofs05PolynomialPartition.lean` | Existing multiplicity correction and collision-safe Fourier argument | `ac807dbef3a481274082e15c19c436e4112b0802` |
| `Proofs05Weyl.lean` | Displayed `lemma_5_3_holds` and its explicit repaired-threshold input | `ad8e18ef177893ba6a88629915693aa4009527e2` |

Search results also located `lemma_5_2_holds` in `Proofs05MissingInterval.lean`. No claim is made that these files were built or independently verified in this session.

The research-directory overview inspected for overlap was:

`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`

Its initially returned blob identifier was `b0edfc23a3624a09c7a2087a336d447a4378622c`. This overview read was from the observed branch, not asserted to be the same pinned revision as every Section 5 source. Its earlier density, cube, arrangement, phase-partition, and rigidity refinements motivated selecting the missing-interval topic. The overlap review is not an exhaustive priority audit.

## Original paper and conventions

W. T. Gowers, *A new proof of Szemeredi's theorem*, GAFA 11 (2001), 465–588, DOI `10.1007/s00039-001-0332-9`.

The original PDF pages with printed page numbers 490–491 were inspected visually. The displayed proof of Lemma 5.2 obtains `t*M/(4*N)`, whereas its printed statement uses `t*M/(2*N)`. The repository target follows the proof-supported factor `1/4`. The manuscript does not call the stronger printed inequality false.

The new extremizers are for an **open** excluded arc. They can charge its endpoints, so they are not automatically equality examples for the original half-open exclusion.

## External mathematical input and related literature

- The explicit Weyl inequality used in the recurrence corollary is the input recorded in `Section05.lean` and supplied by the displayed `lemma_5_3_holds` companion. Its proof is not reproduced in the manuscript.
- Yang and Xie, arXiv:1605.02431v3, provide relevant frequency-selective Toeplitz and truncated-moment context. The general moment criterion is not claimed as new; the required form is proved in the manuscript.
- Baker, arXiv:1602.04245v2, and Maynard, arXiv:2011.12275, are cited to distinguish the local recurrence refinement from the wider and stronger fractional-parts literature.

## Claims not made

No established historical priority for the exact tangent formula; no improved global Szemeredi bound; no best-known monomial-recurrence exponent; no Lean verification of the new statements; no completion of the finite-grid or multiple-arc extremal problems.
