# Normalize the final safe-support word once

> WITHDRAWN FROM RECOMMENDATIONS at closing pin `3b51c69d42ff99bc420698532af3fe1d1f9bd356`. This directory is screened-out audit evidence only. The checked numerical theorem remains valid, but the new incoming boundary-conservation proposal already supplies its claimed normalize-once architectural payoff once assumed applied. Do not count its adapter or metrics as recommended simplification savings. See `../late-head-audit.md`.

## Checked result

`AggregateSafeSupport.lean` passes Lean 4.32.0 using the repository-pinned
Mathlib cache. Every declaration in that file elaborated; the two reported
endpoint axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`.
There are no axioms, `sorry`, `admit`, or `native_decide` declarations in it.
The source hash and precise scope are in `validation.json`.

The generic theorem keeps the actual field constants 977, 2011 and 2022 but
generalizes the radix and kernel. Let M=2011N, rho>=2, K<rho^2022, N>0, and
let S be a finite set of distinct cells satisfying

    j.val+1 < N,    j.val+s < N.

Then, with D=rho^977 * sum(j in S) (rho^2011)^j.val,

    (K+rho^(2011*s))*D < rho^(M-2).

No support-cardinality bound is needed. N=1 and an empty support are covered,
as are stride zero, all admissible cells enabled, and K=0.

## Proof and structural consequence

1. The two exponent functions 2999+2011*j.val and
   977+2011*(j.val+s) are injective on cells. Safety bounds put them below
   M-3 (in fact below M-1022 and M-1033, respectively).
2. The sum of rho-powers at any distinct exponents below L is below rho^L.
   This uses a finite image/range inclusion and the ordinary geometric identity.
3. The kernel and temporal contributions are each below rho^(M-3), hence
   their sum is below 2*rho^(M-3)<=rho^(M-2).
4. The previously proposed no-wrap capacity lemma combines this bound with
   the existing original-word top bound F<rho^(M-1).
5. The existing two actual modular transports then identify F' with
   F+(K+rho^(2011*s))*D. No intermediate normalization is constructed.

The source change deletes `exists_normalization_sum`'s induction over
existential carry/digit witnesses, proves `finite_normalized_increment`
directly from the aggregate estimate, and invokes
`CurrentCarryConstruction2011.exists_assembled_normalization` exactly once
for the final Boolean word.

## Counterfactual novelty boundary

All earlier suggestions are assumed available. The geometric bound is not
new; packet zb already favors geometric identities. The weighted point update
from zn and the incoming two-window capacity simplification are also baseline.
The additional obligation is controlling **the complete ordinary increment
for an arbitrary safe finite support**, which enables deletion of an induction
whose state is existential carry witnesses. Packet zq already proposes larger
subset coverage; this aggregate proof accepts arbitrary subsets, so it also
works after that earlier design removes the optional arithmetic Boolean term.
The earlier reset/locality proposal zo concerns evaluation within independent
cells, not the complete ordinary no-wrap bound.

## Honest cost and validation boundary

The complete target module candidate changes 181 to 156 physical lines,
including one new import: 25 lines removed in that client. The supplied generic
helper is 122 lines, including comments and the baseline geometric/capacity
lemmas; including it literally yields **97 extra lines**, not net compression.
This is a proof-architecture option whose value is eliminating recursive
normalization-witness bookkeeping and supplying a reusable stronger theorem.
Do not present it as an immediate repository-wide line reduction. A smaller
integration can reuse existing envelope/capacity APIs, but no such saving has
been measured here.

`CurrentFiniteDummyMutation2011.candidate.lean` and `normalize-once.patch`
are exact-source integration proposals at commit
`96520cd1a5179f470b4da127bd47bc26a8d808ff`; their actual project imports and
downstream clients were **not compiled**. The helper should be installed as
`Lean/DiophantineConsistency/AggregateSafeSupport.lean` for that import path.
The patch itself does not add this new helper file. Review the generic theorem,
then compile the real target and its Checks file before integration.

`AggregateSafeSupport.lean.log` reproduces the successful compiler's complete
standard output from the second, corrected check. The first check failed on
type-inference and rewrite-direction issues; its result is not claimed as
validation. No upstream files were changed.
