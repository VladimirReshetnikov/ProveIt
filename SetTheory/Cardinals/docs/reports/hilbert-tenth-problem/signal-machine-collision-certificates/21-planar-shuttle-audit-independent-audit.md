# Independent audit of the binary planar shuttle

Date: 2026-10-03. This is a new successor-research audit; no closed report was edited.

## Verdict

The four proposed component rewrites define an unambiguous, translation-invariant binary cellular automaton on the full shift `{0,1}^{Z²}`, with Chebyshev radius at most 6. They conserve the number of occupied sites on every finite configuration. There is no output-overlap obstruction, even when a finite moving component is near a frozen infinite component.

For every integer `k ≥ 7`, the stated four-particle initial configuration reaches the claimed sections at exactly the stated times. The visited set and its centered-square counts admit the explicit formulas below. No reversibility or minimum-radius assertion is made.

## 1. Definitions and uniqueness

For a set `S ⊆ Z²`, join two different points by an edge when their Chebyshev distance is at most 2. Let the connected components of this graph be the occupied components. The four input/output pairs are:

- E: `{(0,0),(1,0)} → {(1,0),(2,0)}`
- W: `{(0,0),(2,0)} → {(-1,0),(1,0)}`
- R: `{(0,0),(1,0),(3,0)} → {(-1,0),(1,0),(4,1)}`
- L: `{(0,0),(2,0),(4,0)} → {(0,1),(3,1),(4,1)}`

Write these pairs `(P_i,Q_i)`. Replace a component equal to `a+P_i` by `a+Q_i`; leave any other component unchanged. All four input sets are connected under the stated graph rule. E and W differ by their horizontal gap; R and L differ by their sorted horizontal gaps. Different cardinalities separate the two pairs. Thus none are translates of another. Each is finite and has a unique leftmost point, so its translation vector is unique. Accordingly, every component has at most one applicable rewrite.

## 2. No collisions; finite-input conservation

Every site of `Q_i` lies at Chebyshev distance at most 1 from some site of `P_i`. This is true by direct inspection, including both the horizontal and vertical moves in R and L. A frozen output site is at distance 0 from its input component.

Distinct occupied components `C,D` satisfy `d∞(c,d) ≥ 3` for all `c∈C,d∈D`. If their output sets shared a point `z`, there would be `c∈C,d∈D` with `d∞(c,z)≤1` and `d∞(d,z)≤1`. The triangle inequality would give `d∞(c,d)≤2`, a contradiction. This argument works for finite or infinite frozen components without alteration.

Each individual rewritten output contains the same number of distinct sites as its input, and a frozen component does as well. The component outputs are pairwise disjoint. Summing their cardinalities proves `|F(S)|=|S|` whenever `S` is finite.

Outputs of distinct components may become distance 1 or 2 apart and thus merge into a larger component at the next time. That is permitted; it is not an overlap or a violation of the rule. In particular, a moving component can merge with an arbitrary frozen component and subsequently freeze. No persistent separation claim is needed.

## 3. A full-shift radius-6 realization

For finite `P`, let `N₂(P)={z:d∞(z,P)≤2}`. For each pair `(i,a)`, define the finite recognition predicate

`r(i,a;S) = [a+P_i ⊆ S and (N₂(a+P_i) \ (a+P_i)) ∩ S = ∅]`.

Because `P_i` is connected, this predicate holds exactly when `a+P_i` is a whole occupied component. In particular, deciding whether a component is infinite is never necessary.

For a site `z`, the rule is equivalently:

- Delete its old occupation if any true recognition predicate has `z∈a+P_i`
- Put an occupation at `z` if any true recognition predicate has `z∈a+Q_i`
- Otherwise preserve its old occupation

Formally,

`F(S)(z) = added(z) OR (1_S(z) AND NOT removed(z))`,

where `removed` ranges over candidates with `z∈a+P_i` and `added` over candidates with `z∈a+Q_i`. There are only finitely many such candidates, since `a=z-r` for `r∈P_i∪Q_i`.

Every recognition needed at `z` reads only `N₂(a+P_i)`. Its maximal required radius is at most

`2 + max{d∞(p,r): p∈P_i, r∈P_i∪Q_i}`.

The resulting bounds are E: 4; W: 5; R: 6; L: 6. Thus the displayed Boolean formula is a uniform radius-6 local rule on every binary configuration, including those with infinite components. The formula has no dependence on absolute coordinates, so it is translation invariant. The component and local descriptions agree, by the exact recognition equivalence and the no-overlap proof.

## 4. Exact orbit and section times

Fix an integer `k≥7`. Define

`K_n=k+n`,

`T_n=n²+(2k−11)n`,

`S_n={(0,n),(3,n),(4,n),(K_n,n)}`.

The claimed initial state is `S_0`. A complete round starting at `S_n` has the following states, with `K=K_n`.

### East phase

For integers `0≤j≤K−6`, at time `T_n+j` the state is

`{(0,n),(3+j,n),(4+j,n),(K,n)}`.

For `j<K−6`, the middle adjacent pair is an isolated E component: its distance to the right singleton is at least 3, and its distance to the left singleton is at least 3. Thus it advances east. At `j=K−6`, the right three points form the translated R input `{K−3,K−2,K}` on row `n`. The left singleton is still separated, since `K−3≥4`.

### R transition and west phase

One R step gives, at time `T_n+K−5`,

`{(0,n),(K−4,n),(K−2,n),(K+1,n+1)}`.

For integers `0≤j≤K−6`, the states at times `T_n+K−5+j` are

`{(0,n),(K−4−j,n),(K−2−j,n),(K+1,n+1)}`.

For `j<K−6`, the middle gap-two pair is an isolated W component. The elevated right singleton is initially distance 3 from that pair and only gets farther away. The pair stays at least distance 3 from the left singleton until the last displayed state.

At `j=K−6`, the lower three points are `{(0,n),(2,n),(4,n)}`, exactly an L input. The elevated right singleton is separate, since its horizontal gap from 4 is `K−3≥4`.

### L transition

One L step produces

`{(0,n+1),(3,n+1),(4,n+1),(K+1,n+1)} = S_{n+1}`.

There are `K−6` E steps, one R step, `K−6` W steps, and one L step. Hence

`T_{n+1}−T_n = 2K−10 = 2n+2k−10`.

Summing from `T_0=0` gives `T_n=n²+(2k−11)n` exactly. Each phase has been justified by whole-component recognition, so this is a proof of the orbit and excludes unintended rewrites. Since `K≥7`, the lower bound needed in every separation check holds for every round.

## 5. Exact visited set

Let `V=⋃_{t≥0} F^t(S_0)` be the set of all sites ever occupied. Row `n` is active during round `n`; once the L step finishes, no later state occupies that row. Its sites are exactly

`V ∩ (Z×{n}) = ({0} ∪ {2,3,…,k+n−2} ∪ {k+n}) × {n}`

for every `n≥0`; no row `n<0` is visited.

Indeed, E fills the horizontal range from 3 to `K−2`, while W fills the remaining point 2 and visits no point beyond that interval. The two wall sites on that row are 0 and K. The only one-row-up R output is the next round’s right wall, and the L outputs are precisely the next section’s other three sites.

Therefore

`V = {(0,n):n≥0} ∪ {(x,n):n≥0, 2≤x≤k+n−2} ∪ {(k+n,n):n≥0}`.

In particular, x=1 and x=k+n−1 are never visited on row n.

## 6. Centered-square counts

For integers `N≥0`, define `C_k(N)=|V∩([-N,N]²∩Z²)|`. Counting by rows gives the universal formula

`C_k(N)= Σ_{n=0}^N [1 + max(0,min(N,k+n−2)−1) + 1_{k+n≤N}]`.

An explicit piecewise simplification is:

- `C_k(0)=1`
- `C_k(N)=N(N+1)` for `1≤N≤k−2`
- `C_k(N)=[N²+(2k−1)N−k²+3k−4]/2` for `N≥k−1`

For the last case, begin with the baseline `N(N+1)`, subtract the triangular deficit `(N−k+2)(N−k+3)/2`, and add the visible isolated-right-wall count `max(0,N−k+1)`. Simplifying gives the expression above, including `N=k−1`.

Consequently, the centered-square asymptotic density exists and is

`lim_{N→∞} C_k(N)/(2N+1)² = 1/8`.

This is the density for these specified centered squares; no assertion about another averaging convention is implicit.

## 7. Optional finite-time trace count

At section time `T_n`, rows `0,…,n−1` have been fully visited and each row `j` contains `k+j−1` visited sites. Row n has exactly the four section sites. Thus

`|⋃_{0≤t≤T_n} F^t(S_0)| = n(k−1)+n(n−1)/2+4 = (T_n+8n+8)/2`.

Also, every fixed site is eventually vacant: the entire support rises to the next row at the end of each round. This does not conflict with the positive centered-square density of the all-time visited set.

## 8. Executable independent checks

`independent_audit.py` implements the component rule, independently implements the radius-local Boolean rule, asserts local read radius 6, checks unique recognition and no output overlap, and compares every phase of 24 orbits (`k=7,…,30`) through 25 rounds with the formulas. It also tests exhaustive small finite configurations, additional random configurations, near-frozen-component cases, visited-row formulas, and centered-square counts.

Finite tests supplement rather than replace the proofs above. The test result is recorded separately in `check-results.txt`.
