# Theorem: role-weighted rank-ULC for total preorders of actual degree at most three

## Statement

Let T be any finite total preorder. Assign arbitrary strictly positive tail activities u_i and head activities v_i. Define

    gamma_k(T;u,v) = sum_(A,B) u_A v_B,

where the sum is over ordered disjoint k-subsets A,B admitting a matching along the off-diagonal arcs of T; each support pair is counted once, regardless of how many matchings witness it. If d is the actual degree of Gamma_T(z)=sum gamma_k z^k and d<=3, then

    gamma_k / binom(d,k)

is log-concave. Single-vertex activities x_i are included by u_i=v_i=x_i.

This is an exact computer-assisted theorem with a small structural reduction and independently checked rational certificates. It is not a finite grid test and does not assert real-rootedness.

## Proof overview

1. The undirected comparability graph of a total preorder on n vertices is K_n. Strictly positive activities preserve the support set, so d=floor(n/2). Consequently d=3 requires n=6 or n=7.
2. The weighted directed-arc Motzkin–Straus argument proves gamma_1^2>=4 gamma_2 in actual degree two and gamma_1^2>=3 gamma_2 in actual degree three. Degrees zero and one are vacuous. To see the first-gap argument directly, form the graph on directed arcs with adjacency when physical endpoints are disjoint, and assign arc i->j weight u_i v_j. Its clique number is d. Weighted Motzkin–Straus bounds the sum over adjacent arc pairs by (d-1)gamma_1^2/(2d), while that sum dominates gamma_2 because every support has a witness of the same weight. The sole remaining inequality is gamma_2^2>=3 gamma_1 gamma_3.
3. An ordered positive composition of n gives the sizes of the successive equivalence classes and covers every total preorder up to relabeling. Since all activities are free variables, relabeling does not restrict the weights. There are 32 compositions at n=6 and 64 at n=7.
4. The exact boundary identities in `BOUNDARY_REDUCTIONS.md` replace an initial or final equivalence block of size two or three by a strict chain while preserving the entire role-weighted gamma polynomial after changing activities. These reductions depend only on identical neighborhoods above/below the boundary block. Effective activities may be zero; the target polynomial inequalities hold on the closed nonnegative orthant, so this causes no problem. Order duality exchanges the two role-activity families.
5. Boundary refinements and duality reduce the 96 ordered compositions to 24 target compositions: 9 on six vertices and 15 on seven. Exact rational nonnegative identities prove the second gap for every target.
6. The target identities are independently verified from Hall-based support enumeration, and a separate cut-position enumeration verifies that all 96 compositions have a valid reduction path to a checked target. Combining the inequalities proves the theorem.

No padded degree-three argument is used for degree-two cases. If a transformed activity vanishes, equality of polynomials preserves the original positive-weight degree-three polynomial; independently, the certificate itself remains nonnegative at all zero-weight faces.

## The boundary-three identity in brief

For an initial size-three equivalence block, order its tails as x<=y<=z, set

    a=sum_(i!=j) u_i v_j,
    c=sum_j v_j xyz/u_j,
    Delta=z(x+y)-xy,

and replace the block by a strict three-chain with unchanged tails and heads

    v2'=[(x+y)c-xy a]/[x Delta],
    v3'=[z a-c]/Delta.

Then its only non-pure-tail admissible local states have unchanged weights

    x v2'+(x+y)v3'=a,
    xz v2'+xy v3'=c.

The ratio c/a is a positive weighted average of yz/(y+z), xz/(x+z), xy/(x+y), establishing v2'>=0 and v3'>0. The first head is unused. Surplus tails have identical neighborhoods above the block, so equality of these local coefficients preserves every continuation. The size-two reduction is v2'=v2+u2v1/u1. Full proofs and exact independent checks are in the boundary document and verifier.

## Exact certificate form

For each target, let w=(u_1,...,u_n,v_1,...,v_n) and

    p(w)=gamma_2(w)^2-3 gamma_1(w) gamma_3(w).

Its stored identity has the form

    p(w)=sum_l q_l w^(m_l) [sum_a c_(l,a) w^a]^2 + sum_e r_e w^e,

with q_l>0 rational, c_(l,a) rational, r_e>=0 rational, and nonnegative integral exponent vectors. The nonnegative remainder is reconstructed exactly rather than redundantly stored. Thus every summand is nonnegative on the nonnegative orthant.

Across the 24 selected target certificates there are 793 square terms and 50,660 positive remainder monomials. These figures refer to the consolidated, authoritative target set; exploratory redundant certificates elsewhere in the directory are not required by the proof.

Production used floating-point LP only to propose square directions and coefficients. At zero numerical residual, active linear equations were reconstructed and solved over the rationals where needed. A candidate was accepted only after its complete rational identity passed exact coefficient verification. Independent verification does not import or invoke the LP producer or any numerical library.

## Authoritative files and reproduction

- `role_total_degree3_complete_verification.json`: complete coverage manifest and all 24 target audit results
- `verify_role_total_cover.py`: independent exact support/certificate/coverage verifier
- `verify_total_certificates.py`: its standard-library Hall support and rational identity kernel
- `BOUNDARY_REDUCTIONS.md`: structural identities and positivity proof
- `verify_boundary_reductions.py` and `boundary_reduction_verification.json`: independent exact Hall checks of both identities and their duals
- the 24 `sos_role_*.json` files named by the coverage manifest
- `role_total_degree3_proof_bundle.zip`: standalone reproduction package with those files

Run, with standard Python only:

    python verify_boundary_reductions.py
    python verify_role_total_cover.py

The first checks 480 exact original/refined and order-dual polynomial identities, including 16 zero-effective-activity cases. The second independently enumerates all weighted support monomials for every required target using Hall's condition, verifies all rational nonnegative identities, and checks complete coverage of all 32+64 compositions via an independent bit-cut enumeration.

## Scope and attribution

The support interpretation, matching-degree bridge, first-gap method, and classical real-rooted families are adaptations of established theory. This finite weighted total-preorder theorem is what these exact artifacts establish; no exhaustive novelty or priority claim is made. Related Ferrers-board, rook-matroid, and weighted Catalan/Motzkin literature was checked without identifying a theorem directly covering the physical disjoint-role condition; see `SEARCH_STATUS.md`.

Still open in this investigation: arbitrary non-total preorders of actual degree three under positive activities, and arbitrary role-weighted total preorders in degree four or higher. Independent-role real-rootedness for arbitrary chains is also not proved here. The separate all-rank real-rootedness results for single-vertex chains and role-weighted rectangular relations remain valid as proved in `POSITIVE_RESULTS.md`.
