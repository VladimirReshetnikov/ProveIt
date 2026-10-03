# Role-weighted boundary equivalence-block reductions

These are exact support-polynomial identities, valid in all ranks. They do not assume real-rootedness or rank-ULC. All original tail/head activities are strictly positive. Effective activities after a reduction may be zero; inequalities proved polynomially for all positive activities extend to these limits by continuity.

## Common mechanism

Let an initial equivalence block B be below every other vertex of a total preorder. No source above B can match a head in B. A local choice of a tails and b heads is therefore admissible only if a>=b. Any b local tails can match the b local heads; all surplus tails have the same outgoing neighborhood above B. Thus, after summing local activity weights, the continuation depends only on (a,b), not on which particular vertices are tails or heads.

Preserving the local generating coefficients for every pair (a,b) with a>=b consequently preserves the entire role-weighted gamma polynomial, with every later equivalence block and every later activity left fixed.

## Initial block of size two

Give the two vertices tails u1,u2 and heads v1,v2. Replace the equivalence block by a strict two-chain, keeping both tails and setting

    v2' = v2 + u2 v1/u1.

The first head is unused in the strict chain and can have any positive value. Pure-tail local weights 1, u1+u2, u1u2 are unchanged. The sole remaining possible local state is one tail and one head; its weight is

    u1 v2' = u1 v2 + u2 v1.

Hence Gamma is exactly unchanged.

By order duality, a final size-two block can be replaced by a strict two-chain, keeping its heads and setting

    u_(n-1)' = u_(n-1) + u_n v_(n-1)/v_n.

The last tail is unused after refinement.

## Initial block of size three

Permute the block's vertices so its tail activities are x<=y<=z. Permuting vertices inside an equivalence class changes no support polynomial. Let the original head activities remain paired with their original tails when computing

    a = sum_(i != j) u_i v_j,
    c = sum_j v_j xyz/u_j,
    Delta = z(x+y)-xy > 0.

Replace the block by a strict three-chain with the same ordered tail activities x,y,z and effective heads

    v2' = [(x+y)c-xy a]/[x Delta],
    v3' = [z a-c]/Delta.

The first head is unused and can be assigned any positive number.

Pure-tail local weights are unchanged because their coefficients are the elementary symmetric polynomials of x,y,z. Aside from those states, a size-three block permits only (a_count,b_count)=(1,1) and (2,1). In the original equivalence block their weights are respectively a and c. In the refined strict chain they are

    x v2' + (x+y) v3' = a,
    xz v2' + xy v3' = c.

These identities follow directly by substitution. The common mechanism above proves equality of the complete gamma polynomials.

For positivity, c/a is a weighted average (with positive weights v_j(sum of the other two tails)) of

    yz/(y+z), xz/(x+z), xy/(x+y).

Every quantity lies between xy/(x+y) and z, with strict upper inequality. Thus v2'>=0 and v3'>0. Also Delta>0 since z>=max(x,y)>0. If x=y=z, then v2'=0: this is an allowed limiting activity and must not be described as strictly positive.

The final-block size-three reduction follows by reversing the total preorder and interchanging tail/head roles, applying this construction, and reversing back.

## Exact independent checks

`verify_boundary_reductions.py` independently counts every weighted support using Hall's condition and exact rational arithmetic. It checks the original and refined polynomials, then independently checks their order-dual versions. Summary in `boundary_reduction_verification.json`:

- 160 initial size-two tests and 160 final size-two tests
- 80 initial size-three tests and 80 final size-three tests
- 16 deliberately equal-tail cases with zero effective second head
- All checks passed

These finite checks corroborate the displayed general proof, rather than replace it.

## Limits

This is a boundary-block reduction. It does not justify refining an arbitrary interior equivalence block by the same formula: heads there may be matched from below. It also does not give a size-four boundary reduction; for example, a four-element equivalence block has a two-head/two-tail local state that cannot be captured by the size-three two-parameter argument.
