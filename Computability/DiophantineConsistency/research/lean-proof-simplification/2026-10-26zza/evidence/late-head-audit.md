# Closing novelty audit at 3b51c69

## Decision

Retain three recommendations: the two local Pell proof changes and the canonical residue criterion/decoder. Withdraw the aggregate-bound/normalize-once direction from the recommendations. The newly submitted exact boundary-conservation proposal supplies its architectural payoff once the user-required counterfactual baseline is applied. A mathematically different numerical estimate is insufficient novelty when its advertised proof simplification already follows from an excluded proposal.

This audit freezes the repository at commit `3b51c69d42ff99bc420698532af3fe1d1f9bd356`, whose committer time is `2026-10-26T19:32:32Z`. The main source audit used `96520cd1a5179f470b4da127bd47bc26a8d808ff`. This is a closing verified snapshot, not a claim that the branch will remain unchanged.

[Exact GitHub comparison](https://github.com/VladimirReshetnikov/ProveIt/compare/96520cd1a5179f470b4da127bd47bc26a8d808ff...3b51c69d42ff99bc420698532af3fe1d1f9bd356)

## Changes in the closing interval

The GitHub comparison contains 13 commits and 13 changed paths. Five maintained Lean modules changed: `ArithmeticNonzero.lean`, `CurrentKernelResidues2011.lean`, `CurrentPowerCoordinates2011.lean`, `PrimePowerOrder.lean`, and `WangTiles942PhysicalOrder.lean`. Their edits adopt already excluded integer-square positivity, common-modulus literal certificates, exact-order endpoint reuse/CRT transport, guarded cast fusion, and finite linear-order rigidity. The adoption ledger and review log also changed. Six incoming ZIPs were added; no new research packet directory was added in this interval.

None of the four candidate source files changed. Their closing blobs were fetched separately and matched the original local bytes:

| Direct source target | Closing Git blob SHA-1 | Check |
|---|---|---|
| `ThirteenFreshSeed.lean` | `332a2be844d198b90b1116e494dba2e442bd6028` | unchanged and local bytes match |
| `SignedPellResidue.lean` | `90db8b332e30a54df716ed3b75ef396ee04eb0f8` | unchanged and local bytes match |
| `BoundedForallCertificate.lean` | `028ed12b572f9b48f1d13f4b8520fa0b316e2288` | unchanged and local bytes match |
| `CurrentFiniteDummyMutation2011.lean` | `441e8cb3a19ed45c01a6352d47df9283d5aac499` | unchanged and local bytes match |

Unchanged target bytes establish patch applicability at those locations. They do not establish a production build against every changed dependency. No additional broad compilation was performed for this closing audit.

## Six newly excluded submissions

Each ZIP was downloaded from the pinned closing commit. Both its Git blob SHA-1 and SHA-256 were recomputed. Proposal summaries and substantive proposal sections were reviewed; the JSON records exact report member paths and hashes. A supplementary search of small text/code/patch members supported the screen but was not used as the only novelty test.

| New ZIP in `docs/incoming` | Mechanisms treated as already applied |
|---|---|
| `Lean_Proof_Simplification_Positions_Rank_Rephase_2026-10-26.zip` | Controller position linear arithmetic; native rank lower bound from full exponent growth; same-data rephase by direct source equality; disjoint-sum rewrite cleanup. |
| `ProveIt_Lean_Shape_Windows_Growth_2026-10-26.zip` | Equal leaf-insensitive splitNatural shapes and diagonal metadata; uniqueness of monotone adjacent windows for square pairing/division; growth theorem at full exponent in CurrentPackingRank. |
| `ProveIt_Lean_Simplification_Round6_2026-10-26.zip` | CurrentPackingRank.fourBlocks_cast directly uses NativeSourceMask.packing_four_block, removing an expanded polynomial detour. |
| `ProveIt_Proof_Simplification_Review_2026-10-26.zip` | Derive primitive-recursive computability from a supplied program; replace quantitative mutation safety with exact equal-boundary carry conservation; joint shifted-numerator envelope in FreeCarrierRatio; optional classical constant-predicate endpoint. |
| `lean-residual-guards-2026-10-26.zip` | Recover positive source guards from two literal rows; compare rotation parameters under exact periodicity; internal division uniqueness by interval separation. |
| `proveit-lean-rank-zero-test-2026-10-26.zip` | Native rank upper bound using a nonnegative deficit; zero-test soundness from product/reconstruction without the Boolean row; controller base unit via oddness and power-of-two modulus. |

## Why the aggregate proposal must be withdrawn

The decisive new source is [ProveIt_Proof_Simplification_Review_2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/3b51c69d42ff99bc420698532af3fe1d1f9bd356/docs/incoming/ProveIt_Proof_Simplification_Review_2026-10-26.zip), Git blob `866ad6371aa2f9fb01ae8e77695e4e5ef35a5687`. Inside it:

- `ProveIt_Proof_Simplification_Review/report/ProveIt_Proof_Simplification_Review.tex`, section B, lines 161–243, proposes obtaining ordinary mutation equality directly from physical interior support and equal boundary carries, then deriving nonwrapping afterward.
- `ProveIt_Proof_Simplification_Review/lean/BoundaryConservation.lean`, `increment_of_equal_boundary`, lines 26–38, states the endpoint theorem for an arbitrary natural increment delta. Its hypotheses are the two carry recurrences, equal incoming/outgoing carries, and an exact raw-word increment. It has no coefficient magnitude, digit bound, or modulus inequality premise.
- The report's integration plan, lines 220–231, explicitly calls for reuse of already proposed update and finite-sum APIs. Lines 190 and 224–225 obtain the common zero boundary carry from actual Boolean assemblies and the canonical last-field identification.

### Counterfactual finite-support implication

The report illustrates one initially unused dummy. The following finite-support consequence is an inference from its proposed contract, not a claim that its archive already implements the finite-support adapter:

1. Use the initial all-zero dummy controls and the final `enabled S`. Both are Boolean; `CurrentFiniteDummyMutation2011.enabled_boolean` is already independent of the size of S.
2. Sum the exact raw perturbations over S. For each j, the existing safety assumptions give `j.val + 1 < N` and `j.val + s < N`. Every literal kernel exponent e is at most 2020, so both `977 + 2011*j.val + e < 2011*N` and `977 + 2011*(j.val+s) < 2011*N`. Thus each perturbation evaluates without cyclic folding. Finite linearity gives the raw increment `(K + rho^(2011*s)) * totalIncrement S`.
3. For the temporal term, use `rotation_whole` separately on the initial and final Boolean assemblies. No additivity assertion for arbitrary binary rotation is needed. Any algebraic finite-sum induction is over raw/source identities and does not construct intermediate normalizations.
4. The existing top-field theorem gives zero boundary carries for both endpoint normalizations. Apply `increment_of_equal_boundary` once with the entire finite raw increment. Its conclusion is exactly the ordinary final normalized-word increment sought by `finite_normalized_increment`.
5. For `exists_finite_normalized_increment`, construct the actual final normalization once with `exists_assembled_normalization`, then use step 4. Delete the induction in `exists_normalization_sum`; it no longer supplies any necessary intermediate normalization witness.

No support-cardinality condition is introduced. Empty support yields delta zero; if N=1 the safety premise forces S empty. The argument uses the existing actual-assembly/Boolean hypotheses of the current finite-support clients. It does not claim the same result for arbitrary cyclic words with unequal boundary carry.

The screened numerical kernel remains a valid checked quantitative theorem, and its exponent budget is mathematically distinct from this conservation argument. However, its advertised normalize-once payoff is already available from the assumed proposal above. It must therefore be absent from the recommended list and saving totals. If retained in an archive, label it only as withdrawn audit evidence.

## Why the other three survive

### ThirteenFreshSeed: `pell_eqz` and `dz_val`

The new incoming proposals do not target the two norm-casting blocks in `ThirteenFreshSeed.auxiliary_exists`. The nearest older carrier/affine proposal is packet `2026-10-26ze`; its exact replacement source still retains both original `χ_sq` / `congrArg` / `push_cast` norm blocks. Packet `zk` changes reflected affine structure, rather than replacing these facts with the existing integer Pell API. Reusing `pell_eqz` and `dz_val` at those two blocks remains an additional local proof simplification. Preserve `hAA` where its later cast application still uses it.

### SignedPellResidue: direct subtraction from an additive equation

No new packet proposes the direct `Nat.sub_eq_of_eq_add' hn` use at this proof site. The closest prior SignedPellResidue changes in packets `k` and `m` retain the intermediate positivity/inequality and arithmetic-tactic block. The additive natural equality already suffices for the desired truncated-subtraction identity, so the local edit requires no extra bound hypothesis. Its current compiler status should be taken from the final candidate validation artifact, not this novelty audit.

### Canonical descending-product residue criterion

The substantive new statement is the equivalence, for prime p and arbitrary naturals a and u, between divisibility of the descending product through u and `a % p <= u`. The canonical client decoder is `j i := a i % p`; the forward direction no longer chooses a divisible factor and then clips its index. This exact arithmetic criterion is absent from the six new proposals. Monotone-window uniqueness, controller residue enumeration and source-guard recovery do not prove it.

The nearest earlier packet `n` supplemental cleanup changes the reverse CRT proof and explicitly leaves the falling-factorial branch alone. Earlier general determined-witness elimination is not enough to provide this prime-product characterization: novelty should be claimed for the arithmetic equivalence and its concrete forward decoder, not for the generic idea of eliminating a function witness. The equivalence needs no `u < p` premise; natural truncated subtraction is handled in the proof. The prime itself is still selected by the original argument.

## Archive integrity

| ZIP | Verified Git blob SHA-1 | Verified SHA-256 |
|---|---|---|
| `Lean_Proof_Simplification_Positions_Rank_Rephase_2026-10-26.zip` | `d6d97b6d430dcf077b731ed34cdde06672885d20` | `0012750a52fff7d5545f48aebfdd33cb2befc9a09242498effc697463a7e72de` |
| `ProveIt_Lean_Shape_Windows_Growth_2026-10-26.zip` | `7b48e53905597e2fe26434ea8cf20a0a379d0bf4` | `5c17f57f08b30b183b056148d6552ded82d4dfa7e8bc189b16aa3b469d417467` |
| `ProveIt_Lean_Simplification_Round6_2026-10-26.zip` | `69bf95cc26359b9c2282b6f543d6ece5fb2810e2` | `91afbb5a7deb3885613e97aa097eb5643ad5c1d32ea7aad2ec171ae5257285fc` |
| `ProveIt_Proof_Simplification_Review_2026-10-26.zip` | `866ad6371aa2f9fb01ae8e77695e4e5ef35a5687` | `65b136894ad45087d97a18e34ccdf32baedb9cc93a40089bb284e6b9b5ae2020` |
| `lean-residual-guards-2026-10-26.zip` | `6254dd4057be00fb36eeb584941b5ff946c4bc22` | `74b2c4df610ad2d1b7ab71ee818f3152e793685dc60978908ec0d2490659c2fc` |
| `proveit-lean-rank-zero-test-2026-10-26.zip` | `33d16f119ae113081d29332fcf51172cd1f86494` | `9a9aeb49119ab6fa164de613352d4899bdf067c5751a64f5f61d4f8497e9fc2a` |

## Limits

The audit does not claim every bundled source snapshot was semantically reread, or that the six incoming production patches were compiled. It reads the proposal sections for mechanisms, records source/code evidence where the overlap matters, and performs a supplementary textual search. The exact boundary proposal itself says its production cyclic/convolution adapter is still proposed; the user's instruction to assume earlier ideas applied makes that integration status irrelevant to exclusion. The three retained recommendations remain assessed at the frozen closing snapshot only.
