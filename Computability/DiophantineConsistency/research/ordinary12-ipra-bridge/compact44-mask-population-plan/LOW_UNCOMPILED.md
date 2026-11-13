# Source-pinned plan: symbolic compact low-mask population

This is an uncompiled proof plan, not a theorem. It concerns the finite-list
value defined by `CompactConcreteMask`, not the retained compressed MC or a
graph port. At this observation the relevant SHA-256 pins are:

- `compact44-concrete-mask-prototype/CompactConcreteMask.lean`:
  `7f3c735747e88ecf1dfbf9d6b759a578ec768a857d3d553c06e8656d7be76ece`.
- `compact44-list-mask-prototype/CompactListMask.lean`:
  `34c4d38c265160155a7fa3f99ea3af692c5f3be10b7b77cac211afc199953d4b`.
- `Lean/DiophantineConsistency/ArithmeticMaskConstants.lean`:
  `dcf27b778181091c3fab210b860ba280e121f6bb267975a07e6231b928072825`.
- `Lean/DiophantineConsistency/ArithmeticBinaryPopulation.lean`:
  `515bf6e175802ff0f5f48023ac2f18195d8e3b0727f906e678f0327dd0b9ee45`
.
- `reviews/compact44-concrete-mask-independent-audit/CHECK.json`:
  `38e176a41a83b029d0cf7a9c4f2406ea162b40528b56b3036343a9137b962fb8`.

Proposed Lean proof:

1. Use `ArithmeticMaskConstants.population_ofDigits` on the standard digit
   list `(CompactListMask.digits (2^67) 8807 1063 S)` and its already proved
   per-digit radix bound. This reduces model population to the cast of a
   standard natural list sum of `ArithmeticMaskData.pcF 67`.
2. Prove the three small standard numeral computations, preferably with
   kernel-checked reduction: `pcF 67 (2^67−1)=67`,
   `pcF 67 (2^67−2)=66`, and `pcF 67 (2^67−4)=65`.
3. Prove in Lean that the explicitly defined support S has 985 entries, is
   contained in `[0,8807)`, and contains 1063. Decompose its disjoint ranges:
   942 entries in `[0,943) \ {1}`, 10 in `[983,993)`, 9 in `[1003,1012)`,
   19 in `[1013,1032)` and five exceptional entries. Avoid reducing the
   590,069-bit numeral or deciding an 8,807-element list by expansion; use
   symbolic finite-sum/cardinality identities and the already established
   per-position recipe.
4. The support has 984 ordinary supported positions and one exceptional
   slot; 7,822 positions are outside support. Thus the proposed standard sum is
   `7822*67 + 984*66 + 65 = 589083`. Transfer that exact result through
   `population_ofDigits` and natural casts to obtain population 589083 in each
   IΣ₁ model for the symbolic finite-list mask.

A coherent source-declared provider and matched author/peer proof replay with
explicit direct imports, exact source hashes, reviewed resource limits, and an
independent audit remain necessary. The population of the high mask, equality
of the symbolic low mask with retained MC or the actual graph port, graph
no-carry and internal PRA proof remain separate open obligations. External
byte checks and this arithmetic plan do not establish those Lean equalities.

A reusable source pattern is `MaskPopulation.sum_map_range`: it proves
`((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j` via
`List.sum_toFinset` and `List.nodup_range`. Its `low_mask_population` proof
then sums a pointwise population-plus-defect identity and filters a finite
support. That file is not currently an imported proof of the compact mixed
special slot; adapt the technique to `pcF 67`, with defect 2 at 1063 and 1 at
other supported slots, and keep its own coherent dependency closure explicit.
