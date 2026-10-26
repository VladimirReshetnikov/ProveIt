# Final freshness audit

**Proof and patch snapshot:** `9d9d1123b39927d30363f1dcd53c23f0575c30ee`.  
**Freshness cutoff:** `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`, committed 26 October 2026 at 19:10:07 UTC.

The cutoff is 11 commits ahead of the proof snapshot. The GitHub compare endpoint returned its 300-file limit, so this review used complete, untruncated Git trees to establish the results below. It did not rerun the earlier full audit.

## Registry and relocation

The research registry now contains **43 placed packets**, a through zq. All **36 previously placed packet trees are unchanged**. `docs/incoming` contains only `README.md` (Git blob `65db1b4cbf85b06d48e5f384d09a7dbe8f51ca04`).

| New placement | Previously audited incoming archive | Retained substantive files checked |
|---|---|---:|
| zk | `diophantine-lean-new-obligations-2026-10-26.zip` | 34 |
| zl | `Lean_Proof_Simplification_Power_And_Masks_2026-10-26.zip` | 90 |
| zm | `ProveIt_Lean_Simplification_Round5_2026-10-26.zip` | 109 |
| zn | `proveit-lean-additional-certificates-2026-10-26.zip` | 53 |
| zo | `lean-proof-simplifications-2026-10-26.zip` | 42 |

All **328 retained non-placement files** have Git blob hashes identical to members of the corresponding previously audited ZIPs. The additional `PLACEMENT.md` and `OMITTED.tsv` files are placement records. Omitted or ignored archive members were already covered by the original incoming review. The five archive SHA-256 values and placement/tree identities are in `prior_art_refresh.json`.

The registry comparison also found **two genuinely additional packets**, zp and zq. These were reviewed separately, including both reports and READMEs, supplemental proposal and review notes, candidate Lean code and patches, and the relevant JSON decision ledgers: **40 retrieved text/code files**, all checked against their Git blob hashes. The large inherited inventories, build scripts, compiler receipts and PDFs were not reaudited; the reports' TeX sources were read.

## Additional exclusions

**Packet zp**, `lean-controller-word-refinements-2026-10-26.zip`, proposes all-offset reflected-source normalization; coprimality transport through fixed prime support; translating an arbitrary finite seed to prescribe a sum; and universal LTE divisibility before recovering multiplicative order. Its further-research questions concern reflected support, fixed unit-certificate APIs, translation-invariant seed constraints, and higher lifts.

**Packet zq**, `lean-controller-simplifications-2026-10-26.zip`, proposes fixed-cardinality cyclic subset sums without coprimality using a one-gap staircase; affine coverage with the non-strict endpoint to remove the Boolean arithmetic correction; annihilating powers at fixed CRT factors; a whole-coefficient residue/unit certificate; all-exponent LTE; and a first-lift adapter. Arbitrary-seed translation is an overlapping companion option.

These directions are added to the exclusion baseline. Neither packet proposes the exact split-half shape invariant or the shared monotone-boundary index theorem. The subset-sum `window_covers_modulus` theorem in zq is about the length of a range of attainable sums; it does not identify indices of disjoint monotone windows.

Packet zq's `evidence/late_head_scope_addendum.md:20–26` lists `CurrentPackingRank2011.rank_gt_twice_window` as an existing declaration. Lines 104–106 describe existing rank binding/population scope and expressly add no rank-population theorem. The report and supporting text do not propose the full-exponent bound simplification. This source inventory mention was distinguished from an actual simplification proposal.

## Source comparison

All **519 maintained module blobs** were compared through an untruncated Git tree. Exactly five changed:

- `ExecutableJones.lean`
- `JonesSyntax.lean`
- `NativeQuadraticPositions.lean`
- `ObjectPolynomial.lean`
- `SyntaxCoefficients.lean`

There are no added or removed maintained modules. The aggregate import file and the entire `checks` subtree retain their old Git identities. The adopted changes correspond to already excluded Jones evaluation bridges, the last-row native span argument, the sparse-list interpretation bridge, and environment-restriction semantics.

The direct source targets `NaturalExpression.lean`, `ExpressionSize.lean`, `RepresentationSize.lean`, `ObjectDivision.lean`, `ObjectPairingInjective.lean`, and `CurrentPackingRank2011.lean` are byte-identical between the proof snapshot and freshness cutoff. Their exact blob checks are recorded in the JSON. This byte comparison is not a fresh Lean build of the changed dependency closure.

## Effect on the shortlist

1. **Split-half shape balance:** the scoped novelty judgment is unchanged.
2. **Shared monotone windows:** the qualified architectural judgment is unchanged. Generic ordered-semiring division uniqueness remains prior, so division deletion receives no fresh savings credit. Its original incoming taxonomy is now in packet zn with identical content.
3. **Full-exponent rank bound:** the narrow local-cleanup judgment is unchanged. The new zq source inventory does not announce that simplification.
4. **Four-block eliminant:** still excluded as an ordinary implementation of an existing identity/cast interface.

The report should identify **9d9d1123b39927d30363f1dcd53c23f0575c30ee as its proof snapshot** and **60fcb2a69b7f1fdd4c3592ea5f164223cad50abe as its final freshness cutoff**, with a final exclusion corpus of **43 placed packets**. No combined compilation of all prior proposals is asserted.

## Immutable references

- [Research registry](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/README.md)
- [Packet zp report](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zp/report.tex)
- [Packet zq report](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zq/report.tex)
- [Packet zq late source-scope addendum](https://github.com/VladimirReshetnikov/ProveIt/blob/60fcb2a69b7f1fdd4c3592ea5f164223cad50abe/Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26zq/evidence/late_head_scope_addendum.md)
