# Closing incoming review A: positions/rank/rephase and shape/windows/growth

**Cutoff:** `3b51c69d42ff99bc420698532af3fe1d1f9bd356`. **Policy:** every outcome proposed in either archive is assumed fully applied, including tentative, optional, withdrawn, notes-only and future directions and real-client adapters. Authors' claims of novelty and compilation are historical claims, not this audit's conclusions. Fresh target names do not rescue an old broad mechanism.

## Exact scope and receipts

The companion `CLOSING_A_COVERAGE.json` inventories 917 extracted files (872 in Positions, 45 in Shape), with actual SHA-256, Git-blob hash, byte count and read classification for each. Complete-file reads: **60 files / 328,460 bytes**: 28 reports/substantive notes, 26 proposal kernels/candidates/patches, four novelty/variant metadata files, two adoption-history patches. **799 historical files** are bound to a byte-identical file in an earlier local round; they were not represented as newly reread. One duplicate helper is bound to a completely read file. The remaining 56 administrative/validation/search files are inventory-only. One historical library snapshot, `baseline/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1984/Identities.lean`, has no prior local byte-identical match and is inventory-only, not a fresh proposal. No Lean, incoming script, build or other artifact was executed; no network request was made.

Packet aliases below:

- **P:** `Lean_Proof_Simplification_Positions_Rank_Rephase_2026-10-26.zip`, member root `Lean_Proof_Simplification_Positions_Rank_Rephase`.
- **S:** `ProveIt_Lean_Shape_Windows_Growth_2026-10-26.zip`, member root `ProveIt_Lean_Shape_Windows_Growth_2026-10-26`.

Their proof snapshot is `9d9d1123b39927d30363f1dcd53c23f0575c30ee`; their own historical comparison cutoff is `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`. Neither is the current cutoff. The semantic ledger below conservatively includes material the authors themselves withdrew or did not promote.

## Excluded mechanism ledger

### CA01 — Fixed-literal affine physical positions

**P:** `safety/README.md`, `report/inputs/03-positions.tex`, all three safety patches, full `safety/candidate/CurrentControllerPositions2011.lean`, initial/final novelty metadata.

The retained proofs unfold the small fixed controller prime and `pow_succ`, keep large powers symbolic, and solve a linear coefficient problem with `omega`. `position_budget` uses the index bound `j.val+1 ≤ p^k`; `position_injective` cancels the actual fixed affine step by literal arithmetic. Exclude the complete family and its physical/controller adapters, not just the two retained theorem names. Initial optional proofs of `optional_next_lt`, `optional_stride_lt`, and `position_ne_three` are also excluded even though the packet withdraws them after zq's optional-support retirement. A discarded subchange remains prior art under the present rule.

### CA02 — Full-exponent growth specialization and every new client of it

**P:** population README, `report/inputs/05-population.tex`, rank patch and candidate. **S:** report section C, `growth/numeric_notes.md`, isolated `FullExponentGrowth.lean`, growth patch and full `CurrentPackingRank2011.lean`; report follow-on at line 357.

Normalize `q^3` to `2^(3*u)` and use `2*u ≤ 3*u < 2^(3*u)`, applying `Nat.lt_two_pow_self` once at the full exponent. This deletes positivity/base-square detours while preserving the actual top-block lower bound and natural/integer cast bridge. All natural-subtraction domain guards and the enclosing theorem's public premises stay intact; the isolated growth inequality also holds at zero. Reserve the expressed broader search family: a final `b^(k*u)` and a linear bound in `u`, replace staged exponent growth with one library theorem plus normalization/linear arithmetic, checking zero/boundaries. **Already excluded by the earlier packet zc broad normalization + growth + omega family regardless of these authors' target-specific novelty advocacy.** Do not credit it again because the constructed rank is before source/Pell hypotheses.

### CA03 — Exact rephase field transport

**P:** rephase README, `report/inputs/06-rephase.tex`, rephase patch and full candidate.

Within `CurrentWordRephase2011.normalization_of_rotation_eq`, avoid a separately proved function equality for `raw`; use the given rotation equality directly in recurrence and decomposition record fields with `simpa only [CurrentCarryConstruction2011.raw, hr]`. Bounds are inherited unchanged. The scalar transport block, same source/carry/digits, and ordinary multiplier quotient distinction remain explicit. Exclude the local record-field transport mechanism and its actual adapter, not merely a theorem-name occurrence. Also reserve discussed but unpromoted rotation quotient/remainder alternatives, Boolean-premise removal and cosmetic scalar modular chaining; the first two overlap the already read initial manuscripts. No equality of old/new ordinary multiplier, preservation of the old quotient, or new coherent witness can be inferred.

### CA04 — Disjoint addition by the existing bitwise identity

**P:** population README, `NativePackingPopulation` candidate and `disjoint_add_lt.patch`.

Rewrite the existing `add_eq_land_add_lor` identity using the zero-AND premise, then use the unchanged OR-width bound. This is optional housekeeping, but is excluded just as fully as a promoted result. It does not supply a new mask API or new semantic theorem.

### CA05 — Exact raw split shape and scalar reachable metadata

**S:** report section A, `shape/ShapeCore.README.md`, independent shape review, `SplitShape.lean`, `ExpressionSize.lean`, `ShapeCore.lean`, shape patch.

The two *raw* `Expr.splitNatural` outputs have equal ordered, operation-labelled shapes after constants and variables are all erased to one leaf. A generic fold can use arbitrary leaf/add/mul values with no algebraic laws. The multiplication case produces the same `add(mul P Q)(mul P Q)` shape after inductive hypotheses. Consequences include exact equality of both halves' counts, depths, witness counts, addition/multiplication counts, and every leaf-insensitive structural cost; the reviewed asymmetric GraphRep depth recursion remains covered.

Reachable `SplitSize` pairs lie on a diagonal. Compute `halfSize` once (leaf 1; add/sub `1+Hp+Hq`; mul `3+2Hp+2Hq`) and project both fields from that scalar. Preserve arbitrary off-diagonal `SplitSize` operations and prove equality to the old recursion; propositional equality does not promise identical definitional reduction. Include downstream BoundedForallSize/Depth migrations and the legacy-vs-new implementation comparison kernel as real adapters, not separate novel directions.

**Express follow-ons are excluded:** other paired metadata recurrences constrained to a proper subset of their declared state space, with old/new equality and consumer inventory; a shape-only count/depth/operation-sensitive resource interface; a raw/simplified split-certificate boundary. These are broader than a single `halfSize` target. The result does **not** identify semantic evaluations, variable supports, polynomial degrees, literal-sensitive cost, or independently simplified output trees. The last point has an explicit `x*x` versus zero counterexample.

### CA06 — Shared monotone half-open window index uniqueness

**S:** report section B, windows README, generic `OrderedWindow.lean`, both extracted pairing kernels, full post-y pairing candidate, all compatibility-current-head candidates and patches.

For linear-order indices, preorder codomain, a successor bridge `a<b → succ a≤b`, and monotone boundary `base`, two half-open windows containing the same value have equal indices. Strict monotonicity, well-foundedness, Archimedeanness and codomain antisymmetry are unnecessary. A strict upper bound is essential. Exclude the generic abstraction, direct interval-separation endpoint alternative, and all real adapters:

- max-square shell pairing with lower/next-square bounds;
- pairing after packet y's shell-cut branch recovery (retaining the prior branch cut);
- pre-y four-branch compatibility pairing;
- internal-model division with linear boundaries `q*d`, uniqueness of quotient then additive cancellation for remainder;
- arbitrary semiring kernel and host-Nat example.

The source model remains an arbitrary internal natural carrier, not host `Nat`. Division uniqueness is already old, but is nonetheless included here as a fully applied adapter. Helper overhead is real (22-line helper versus six-line pairing reduction); no future savings may be subtracted from current cost. The explicit *third decoder/disjoint-shell encoding* follow-on is excluded too, even without a shipped client.

### CA07 — Notes-only residual directions, not proposals to resurrect

**S:** `audit/prior_art_notes.md`, particularly its candidate table around lines 107–116; report follow-ons around lines 347–357. Every direction below is reserved despite absent patches or tentative wording:

1. `Polynomial.totalDegree_specializeOne_le` via a general affine-substitution / MvPolynomial `eval₂` degree bound, preferably reusing an existing library theorem rather than moving a handwritten proof.
2. Principal bitset ideal / complement-mask interface using bitwise order and width bounds; require actual clients and full interface cost. Not endorsed as present savings, but still a considered direction.
3. Exact partial-run hitting-time theorem, distinct from merely replacing fixed-none induction by `IsFixedPt.iterate`; explicitly requires comparison with old first-exit infrastructure.
4. A genuinely additional scalar transport obligation for minimal carry Facts, rather than the already old bounds/decomposition/derived-recurrence record.
5. Horner/affine-monoid chunk assembly considered weak or old finite-block novelty; natural simplifier joint correctness/size; source `N=q^3` syzygy; these remain old, not fresh opportunities.

P's inherited ledgers additionally reiterate (without renewing novelty) common terminal-field identities, fixed-modulus and LTE/prime support contracts, translated invariant seeds, physical finite mutation composition, Boolean-free affine coverage, unrestricted-cardinality staircase, first-lift seed and optional-support retirement. They remain fully excluded through the earlier baseline audit. Adoption-history patch reading records earlier source changes, not new proposal mechanisms or fresh compiler validation.

## Requested residual checks

**Existing Pell sequence growth:** No new contribution, optional branch, follow-on or actual adapter in these two packets proposes obtaining `NativeOuterSeedConstruction`'s local `r+1 < yn(r+1)` directly from `PellMod.lt_yn_of_two_le`. Their growth mechanism CA02 is normalization of exponential powers and a linear-vs-exponential estimate; it neither constructs nor bounds this Pell sequence. Historical source snapshots or inherited ledgers mentioning Pell are not, by themselves, a proposal of this local proof. This conclusion is semantic and bounded to the two packets, not based merely on absence of those names and not a global novelty authorization.

**Existing combined coefficient bound:** No new contribution, optional branch, follow-on or actual adapter in these two packets proposes replacing repeated entrywise coefficient estimates by the existing `coeff_combined_at_entry`. CA05 is raw expression-tree shape/resource metadata; CA04 is bitwise disjoint-add arithmetic; CA07's degree substitution is a polynomial degree transport problem. None is the combined-coefficient API reuse mechanism. Earlier coefficient/sum/carry families must still be checked independently by the parent audit; this does not rescue any new client of an old family.

## Validation and honesty limits

P labels its delivered Lean deltas uncompiled. S reports historical isolated checks, with stale-cache/import limitations for larger shape modules, generic kernel rather than arbitrary-model wrapper coverage for windows, and isolated rather than full-module growth checking. These reports were read but not reproduced. This audit asserts no Lean acceptance, savings, upstream adoption or correctness result. Exact output hashes and scope counts should be verified from the companion coverage rather than copied from historical packet manifests whose initial and final candidate hashes can differ.
