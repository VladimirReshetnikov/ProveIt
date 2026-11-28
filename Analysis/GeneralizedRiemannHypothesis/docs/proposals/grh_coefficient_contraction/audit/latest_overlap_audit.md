# Updated novelty audit: the sweep proposal is already present

Latest inspected proposal commit: `1a59f50680e470fb5269bbe70c06f974c95ad930`.
Earlier source-analysis baseline: `d417d0b5b08edd4f5f67224fd310add7f1618ca0`.
The working-tree checkout was not changed. All new documents were read using `git show` at the latest commit.

## Decision

**The original main proposal must not be presented as new relative to the current requested folder.** Both `grh_diagonal_sweep_proposal` and `grh_exchange_sweeps` already prove a canonical first-to-last sweep, charge only diagonal Fourier sums, retain exact diagonal column cardinalities, and preserve the same scalar/period contract. Our max-coordinate shell schedule instead of their min-coordinate strip schedule is an ordering variant, not a substantively distinct simplification.

The broad intrinsic-frontier idea is also already proposed as an explicit further question in `grh_exchange_sweeps`. In addition, `grh_diagonal_sweep_proposal` already states and uses the supported-tuple/dependent-product restriction–zero-extension bijection. Our completed covariance/support/Fourier/contraction calculus goes materially beyond the detail supplied there, but it is a **concrete solution to a stated extension**, not a fresh architectural idea. Under the user's instruction to assume existing proposals implemented, it should be treated as background or implementation support, not used as the headline contribution.

## Documents inspected

The full `report.tex`, `LEAN_PLAN.md`, and `README.md` in each of these two directories were read. Exact copies are in `research/latest_proposals/`; `source_manifest.json` records Git blobs, SHA-256, bytes, and physical line counts.

- `grh_diagonal_sweep_proposal/report.tex`: blob `bd58d29b4ad2606897537373addef4f9ca2bb635`, 244 physical lines.
- `grh_diagonal_sweep_proposal/LEAN_PLAN.md`: blob `973e9fa570f65f308f9e05717f7a14718dd04ec5`, 27 lines.
- `grh_exchange_sweeps/report.tex`: blob `cb5cd5c9d71d959afd5f7b8d391f1a9b76064ebd`, 269 lines.
- `grh_exchange_sweeps/LEAN_PLAN.md`: blob `3cddc5a3276943e159f21ee101e9cb58f4a1d974`, 34 lines.

This note is specifically the overlap analysis of those two new proposals. Other newly added directories are being checked by the other reviewers; their absence from the following table is not an assertion that they were all read here.

## Exact overlap map

| Feature in our draft | Current proposal already containing it | Assessment |
|---|---|---|
| Canonical two-grid sweep replacing arbitrary-path turn search and strong induction | Both reports; diagonal-sweep §3, exchange-sweeps §3 | Fully covered. Their words are `R^j D^(m-j)`, ours `D^(m-j) R^j`; both use the same local laws and exactly all squares. Changing the shell order does not create a new contribution. |
| Every square used once, `m²` turns, exactly `m` diagonal turns | Both schedule proofs | Fully covered. |
| Transfer budget `V^m` instead of `V^(m²)` | Both main sweep theorems | Fully covered. |
| Exact diagonal count `q^[r+(2j+1)t]` and product `q^[mr+tm²]` | Diagonal-sweep §4; exchange-sweeps §4 retains the exact product | Fully covered. Rewriting as `q^[m(n_m−1)]` is just algebra, not a new estimate. |
| Correct backward proportionality implication; constants chosen before data; product of all `turnRatio` factors | Both source-contract sections and proofs | Fully covered. Our care with quantifiers is necessary validation, not novelty. |
| Keep local square law, matching, line reversal and seesaws | Both plans explicitly retain them | Fully covered. |
| Delete `squares`, arbitrary corner existence, `turn_induction`, generic dispatcher | Both integration plans | Fully covered. |
| Stronger first-path coset count and last-path exact edge-matrix count | Diagonal-sweep §5 and phase 3 of its plan | Fully covered and stronger than the coarse endpoint bound retained in our original draft. |
| Bijection between supported ambient tuples and the dependent product of active matrix types | Diagonal-sweep report lines 163–175, plan line 21 | Explicitly stated and used for cardinality. Our broader coefficient-function equivalence is a natural extension, not a new bijection. |
| Active-frontier coefficient representation removing unused edge coordinates and invariance bookkeeping | Exchange-sweeps report line 266, further research paragraph | Explicitly proposed, but not developed into a theorem or implementation. Must acknowledge it. |
| Finite diagonal-closed node group exactly equal to global admissible restriction image | Not developed in either report/plan | New technical detail answering the frontier question. Insufficient alone as a major independent proposal. |
| Full fibrewise Fourier–matching transform with spectator action, exact covariance character identity and split-support proof | Not developed in either report/plan | Concrete new resolution of the frontier question, but the underlying construction and identities already exist in source `Corner`; cannot fairly describe the broad simplification as previously unproposed. |
| Finite local contraction identity for arbitrary correlated coefficients, typed spectator/test dependence | Not stated in either new report/plan | Useful implementation lemma; mathematically finite distributivity and existing square law. It supports the frontier extension rather than changing the assumed post-proposal proof strategy. |
| Exact joint terminal class-sum equality, then separate integrality and conjugate bounds | Neither report nor plan | Distinct extension still available. Diagonal-sweep changes only the count in the current sum-of-roots/set-nsmul proof and explicitly leaves local integrality unchanged. |
| Replace `IsSumOfRootsOfUnity` by separate algebraic-integrality and uniform conjugate-bound certificates | Neither report nor plan | Distinct extension still available; see recommendation below. |
| Normalize weighted triangular Gram laws | Exchange-sweeps §5 | Already covered; do not propose as a fallback. |

## Distinctions that are not enough

1. **Maximum shell versus minimum strip.** The old report diagonalizes first and then sweeps outward. Our draft sweeps first and diagonalizes last. Both give the same componentwise transfer product. The shape of the loop is not a new proof simplification.
2. **A formula using `n_m` instead of `r,t`.** The exponent identity follows from `k+m=r+1` and changes no bound.
3. **Finite residue ring rather than field.** The diagonal-sweep report already emphasizes that the counts are function-space cardinalities over a finite ring, including empty matrix types.
4. **More extensive finite regression tests.** These improve evidence for a proposed implementation, but do not make an already proposed mechanism new.
5. **Calling the frontier a tensor.** The exchange-sweeps question already asks to retain only active-frontier variables. Naming that representation differently does not avoid overlap.

## Best distinct extension currently supported by our work

The structural reviewer is developing the following proposal, which is not supplied by the two new reports and was not identified in the earlier 21-directory corpus:

> Replace the existential multiset-of-roots arithmetic certificate by the two properties actually consumed downstream—algebraic integrality and a uniform bound under every complex embedding—and prove one exact jointly invariant terminal class contraction. Derive finite-place integrality and archimedean bounds separately from that formula.

This should be formulated after assuming the canonical sweep, active-frontier representation and exact endpoint counts are already available. It must not claim their line savings or their improved exponents again.

A useful coefficient contract is schematically

- `IsIntegral ℤ (F s)`;
- for every complex automorphism `sigma`, `‖sigma(F s)‖ ≤ B`.

Finite root-valued characters preserve both properties. An unnormalized finite Fourier sum multiplies the second bound by the column cardinality and preserves the first; matching is one evaluation times a root of unity or zero. Thus no root multiset or concatenation proof is needed in the transfer. The local geometric support and covariance remain unchanged.

At the terminal stage, retain `FixedByOuterLevels` for the initial forms and the full joint level-invariance hypothesis. The current free-level chain equality can be applied to the two chains, followed by the final free class integral, producing a single finite expression over the boundary tuples and the `2m+1` class variables. This representation preserves correlations and avoids asserting invariance term by term. The integrality proof uses closure of integral elements under finite sums and products; the archimedean proof uses the triangle inequality and the same cardinalities.

The distinction from diagonal-sweep's further question about improving Fourier norms is important: this proposal **does not require a smaller numerical budget or a new normalization**. It weakens the proof certificate to its actual consumers and removes nested sum-of-roots/set-nsmul scaffolding. The proposed change is to the logical/arithmetic interface and endpoint proof, even when all numerical estimates are kept exactly the same.

There remains work before calling this a significant shortening: identify the actual root-certificate consumers and the `nsmul` scaffolding rendered unused, prove the joint terminal equality with source measure normalization, and measure the source replacement scope. Do not carry over the previous 2,862-line footprint as a saving estimate for this narrower independent proposal.

## Required changes to our deliverable

- Retitle around the new coefficient invariant and terminal contraction if this extension succeeds.
- Move sweep and exact coefficient-count formulas to an attributed background section, or remove their full proofs.
- Identify the frontier calculus as implementation detail of the already-posed frontier extension; avoid counting its general idea as novelty.
- State both source baselines: old Lean source analysis and latest proposal audit. If Lean blobs are unchanged, record that fact after checking it rather than assuming it.
- Update the corpus count and inclusion/removal map against the latest commit.
- Retain the old report only as a clearly marked superseded working draft if needed internally; do not deliver it as the main novel proposal.

## Addendum: exact collapse of the initial average

The mathematical reviewer is investigating a stronger independent candidate: prove that the entire initial coset average equals a fixed multiplicity times a root-or-zero coefficient, by uniquely recovering all nonredundant gauge cosets recursively from the boundary tuple. If the multiplicity is independent of the twist (or has an explicitly permitted scalar normalization), divide it out and start the sweep with coefficient budget 1.

This needs a precise novelty distinction. `grh_diagonal_sweep_proposal/report.tex:232` already asks to remove the redundant coset at the reflected initial diagonal node, and explicitly warns that its twist-dependent normalization cannot simply be absorbed into a twist-independent proportionality constant. **That single-factor removal is already proposed.** Assume it implemented.

What is not present in either report or plan is a proof that every remaining nonzero summand has a uniquely determined tuple of gauge cosets, a uniform-fibre theorem for the complete average, the root-or-zero conclusion, or removal of the full initial coefficient-count exponent. Thus a verified theorem of exact collapse of **all** remaining averaging variables would be a materially stronger result beyond the proposed redundant-node deletion and endpoint cardinality improvement. Its headline should be that fibre/uniqueness theorem and its resulting normalized initial datum, not another proposal to omit the already identified redundant variable.

A targeted scan of all six newly added directories' Markdown/TeX texts found no other discussion of `firstPathDatum`, initial coset averaging, or such an exact-fibre collapse. The integral-field and Ribet-lattice reports concern other arithmetic modules; the projective-incidence report's coset/fibre calculations concern the finite-field second-moment inequality, not the initial auxiliary datum. This scan is an additional exclusion check, not a full mathematical audit of those unrelated reports.
