# Closing non-repetition check through 663fb267f6

## Two pins, two purposes

- Original source and comparison pin: `89226e3921bce3e8949fadd12d3efb6914c7630c`.
- Closing corpus refresh: `663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda`.

The GitHub comparison reports 12 commits and 30 changed files. Within the two proposal roots, the changes are exactly one modified adoption record and one new archive:

`docs/incoming/ProveIt_Additional_Lean_Simplifications_2026-10-26.zip`

It arrived in `89f3a32b336bbf9719b35cafe6de19c5a06e9b46`. Its archive wrapper contains `diophantine-lean-proof-interfaces-2026-10-26/`. The packet is 338,715 bytes with 131 non-directory members. Its Git blob SHA is `64f93e46c7524cd0b1323a4814108cc68624962f`; the SHA-256 and all member hashes are in `refresh_corpus_manifest.json`.

The refresh still has 23 placed packets and 1,286 placed files. It now has five incoming archives with 1,042 non-directory members: **28 packets in the closing comparison corpus**. The original corpus inventory is preserved unchanged. The refresh manifest is a delta supplement, not a replacement for the initial snapshot.

The four target source files are unchanged in this comparison: `CurrentSelectorTail2011.lean`, `CurrentWordConstruction2011.lean`, `CurrentControllerData2011.lean`, and `CurrentTileColors2011.lean`. Source edits and measurements therefore remain attributed to the original pin. Unchanged target bytes do not certify unchanged dependency behavior, and no compiler evidence is upgraded to a build of the refresh commit.

## Contents of the additional packet

The report and supplementary reviews were inspected, with targeted searches across the text, Lean examples and patches. Supplied programs were not executed. Its six directions, with report anchors, are:

| ID | Existing idea now additionally excluded | New report anchor |
|---|---|---|
| A | Helical row-zero proof through a period-one orbit | `report/report.tex`:124–163 |
| B | Coprime mixed-sum divisibility: `J*F ∣ Q*F+J*(H-C)` iff the separate divisibilities | `report/report.tex`:164–200 |
| C | Geometric-series identity and deriving its coarse bound without a second induction | `report/report.tex`:201–237 |
| D | Interpret a positive quadratic margin as a linear interval | `report/report.tex`:238–282 |
| E | Finite signed-prefix normalized word as Euclidean remainder, terminal borrow as quotient | `report/report.tex`:283–343 |
| F | Compare the arithmetic `windowRank` using the fixed-parameter scalar `C+q*F` | `report/report.tex`:344–408 |

The later questions also cover signed-prefix concatenation, correlated scalar-rank updates, additional helical orbits, reusable margin endpoints, and local rank-comparison simp rules. None is added to this review's recommendations.

Some of this new packet's directions overlap packets already included in our original comparison, notably periodic helix proofs and geometric-series cleanup. Their arrival does not create new credit for our review, and their validation claims are not replayed or adopted here.

## Check against the four retained ideas

| Retained idea | Closest new-packet material | Closing decision |
|---|---|---|
| Selector-tail cutoff by negating an existing strict comparison | F also concerns a reversed order, but for an affine arithmetic `windowRank` and scalar `C+qF` | Retain. The new packet does not discuss finite selector sorting, `tail_position_iff`, `selectorTail_succ`, the exceptional Start slot, or rewriting these conditional guards. We claim only the exact small client deletion, not a new general theory of order reversal. |
| Supported cell-digit invariants under numeric control-slot overrides | The new packet mentions preserving source digits as a remaining condition for hypothetical rank changes | Retain. It gives no finite-update construction, no invariant for the 977/1004 slots, and no replacement for the constructed-word Boolean/support proofs. |
| Prime-factor certificate for exact multiplicative order | B uses coprimality for cancellation in a mixed divisibility equation | Retain. It does not discuss `orderOf`, `primeFactors`, primality/factor-set certificates or exclusion of prime divisors of an order. |
| Bounded-complement cancellation in actual tile colors | B uses divisibility cancellation; D uses positivity and square/interval conversion | Retain as optional local cleanup. Neither is the guarded injectivity of natural subtraction from 255/511 or the two color-equality clients. |

The updated `ADOPTION.md` changes implementation status and validation descriptions of earlier proposals. Under the user's instruction, these were already assumed available. Status changes introduce no additional simplification mechanism relevant to the four retained deltas.

## Evidence files

- `refresh_compare.json`: full 30-file comparison metadata, including the two proposal-root changes.
- `refresh_corpus_manifest.json`: archive and member hashes, refreshed counts, modified metadata hash, target-source unchanged list.
- `refresh_sections.tsv`: 63 new report/supplementary heading occurrences.
- `ADOPTION-refresh.md`: exact refreshed metadata bytes, verified against Git blob `986f1114f2050b4b05d8a4edded492243c3c379d`.

This is a bounded closing check through the stated commit. It is not a claim about later uninspected arrivals.
