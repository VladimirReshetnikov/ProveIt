# Independent addendum: vertical drift and first arrivals

Keep the notation in `independent-audit.md`, but call its CA `G`. Let `τ(x,y)=(x,y+1)` and set `F=τ∘G`. Translation equivariance gives `F^t(S_0)=τ^t(G^t(S_0))` exactly. All statements below hold for every integer `k≥7`.

## 1. Locality and conservation under drift

Vertical shift is a bijection, so finite-input mass conservation immediately carries over. The radius of F is still at most 6. In the explicit recognition formula for G, relative to the output site, the necessary input coordinates have x offsets in `[−6,6]` and y offsets in `[−3,2]`. Evaluating G at one row below the F output changes the latter interval to `[−4,1]`, leaving all reads in the Chebyshev radius-6 square.

No claim of minimum radius or reversibility is made.

## 2. Four labeled trajectories

At time t let `n(t)` be the round index, characterized by `T_n≤t<T_{n+1}`. Label the three lower-row particles “bulk” and the isolated right wall “marker.” During a round the bulk share row n, and their x coordinates are 0 and the two displayed shuttle coordinates in the phase formulas. Each bulk x satisfies `0≤x≤k+n−2`. At the next L step all three rise to row n+1.

Let `r(t)` be the marker’s G row. Then `r(t)∈{n(t),n(t)+1}`, and its G coordinates are `(k+r(t),r(t))`. It rises from row n to row n+1 at

`ρ_n=T_n+k+n−5`.

For F the bulk vertical coordinate is `h(t)=t+n(t)`, and the marker vertical coordinate is `v(t)=t+r(t)`. Both are strictly increasing; each increases by 1 except for its own upward-jump times, when the increase is 2.

The three bulk traces are pairwise disjoint, since all share h(t), h is strictly increasing, and their x coordinates at a fixed time differ. The marker cannot intersect a bulk trace either. Indeed, suppose its site at time t equals a bulk site at time u, and put `r=r(t)`, `n=n(u)`. Equality of x implies `k+r≤k+n−2`, hence `n≥r+2`. Equality of y implies `u=t+r−n≤t−2`. But then monotonicity gives `n=n(u)≤n(t)≤r`, a contradiction. Thus all four all-time traces are pairwise disjoint and each never revisits a site.

## 3. Exact skipped vertical levels

At a bulk upward jump into section n, the previous vertical height is `T_n+n−2` and the new one is `T_n+n`. Consequently each bulk trajectory visits every nonnegative integer y except

`a_n=T_n+n−1=n²+(2k−10)n−1`, for `n≥1`.

At the marker upward jump at time `ρ_n`, its previous vertical height is `ρ_n+n−1` and its new one is `ρ_n+n+1`. Thus its skipped levels are exactly

`b_n=ρ_n+n=n²+(2k−9)n+k−5`, for `n≥0`.

These sequences strictly increase. They interlace: `a_n<b_n<a_{n+1}` for `n≥1`; also `b_0<a_1`. The differences are `b_n−a_n=n+k−4` and `a_{n+1}−b_n=n+k−5`, both positive for k≥7.

## 4. Why horizontal truncation disappears for N≥k+1

Every F-visited site `(x,y)` satisfies `x≤max(k+1,y)`.

For a bulk site in rounds n=0 or 1, `x≤k+n−2≤k−1`. For n≥2, `T_n≥T_2=4k−18≥k−2`, so `x≤k+n−2≤T_n+n≤y`.

For a marker site with `r≤1`, `x=k+r≤k+1`. For r≥2, the earliest possible time is `ρ_{r−1}=T_{r−1}+k+r−6`. Thus

`y−x≥T_{r−1}+r−6≥T_1−4=2k−14≥0`.

All visited coordinates are nonnegative. Hence, when N≥k+1, membership in the centered square `[-N,N]²` is exactly the condition `y≤N` for every F-visited site. This bound explicitly checks the short initial transient instead of assuming it away.

## 5. Exact drifted centered-box counts

Let

`A_k(N)=#{n≥1:a_n≤N}`,

`B_k(N)=#{n≥0:b_n≤N}`.

By the pairwise-disjoint trace proof and the skipped-level formulas, for every integer `N≥k+1`,

`C_F,k(N)=4(N+1)−3A_k(N)−B_k(N)`.

Writing `α=2k−10` and `β=2k−9`, the exact root formulas are

`A_k(N)=max(0, floor((sqrt(α²+4(N+1))−α)/2))`,

`B_k(N)=max(0, 1+floor((sqrt(β²+4(N−k+5))−β)/2))`.

Both are `sqrt(N)+O_k(1)`. Therefore

`C_F,k(N)=4N−4sqrt(N)+O_k(1)`.

For the generalized inverse `R_k(M)=min{N≥0:C_F,k(N)≥M}`, it follows that

`R_k(M)=M/4+sqrt(M/4)+O_k(1)` as `M→∞`.

For completeness, set `m=M/4` and `u=m+sqrt(m)`. Then `u−sqrt(u)=m+O(1)`, so `C_F,k(u)=M+O_k(1)` in the asymptotic real-variable expression. The exact count changes by at most 4 at an integer step; beyond the initial transient its increment is at least 1, since the two skip sequences never coincide. These facts absorb root approximation and integer rounding into an `O_k(1)` error in the inverse.

## 6. Exact first arrivals for G

For a site on row n let `d=k+n`. The following list covers the entire row of G’s all-time visited set.

For n≥1:

- `x=0,3,4`: first arrival `T_n`
- `x=2`: first arrival `T_n+2d−11`
- `5≤x≤d−2`: first arrival `T_n+x−4`
- `x=d`: first arrival `T_n−(d−6)`

For n=0 the same formulas hold except that the initial right wall x=k first arrives at time 0; the other initial sites x=0,3,4 also have first-arrival time 0 as already specified.

The first three section sites enter row n in the preceding L transition. Site x=2 is reached only at the final W state. Every remaining interior site is reached first by the east-moving pair’s right member. The isolated right marker enters row n during the preceding R transition, at

`T_{n−1}+d−6 = T_n−(d−6)`.

This uses `T_n−T_{n−1}=2d−12`. No earlier state on row n exists apart from that marker, so the first-arrival claims are exact.

## 7. Computational check

`independent_drift_audit.py` imports only the separately written component-rule implementation, simulates G, shears each spacetime state directly to obtain F, and checks:

- no repeated site in the complete drifted trace
- the horizontal bound at every simulated site
- exact centered-box counts and root-count expressions
- the original G first-arrival formulas
- radius at most 6 after the vertical drift

It tests 34 values of k, from 7 through 40, with 701 states each. Its observed output is stored in `drift-check-results.txt`.
