# Independent review of sparse orbit examples and frame restoration

Review date: 3 October 2026

## Verdict and scope

**Pass, conditional on the orbit classification and phase normal form explicitly inherited by the source packet.** I found no blocking mathematical defect in Theorems B–C or the concrete constructions in §§6–9. The examples establish the claims for actual translation-equivariant, finite-radius, globally conservative weighted-alphabet cellular automata. Their distinct-site sets, cross-time collision treatment, exact floor formula, and rank-three sharpness arguments are sound.

This review is bound to `../sparse-orbit-geometry-research-20261003/PROOF.md` with SHA-256

`3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa`.

The complete source fingerprints are recorded in both independent audit receipts. This reviewer did not edit the source packet, its predecessors, or prior releases. The source author resolved one wording ambiguity reported during review: §7 now explicitly changes the horizontal right-bounce destination **and its vacancy guard**, and explicitly removes the obsolete vertical vacancy guards at the horizontal left bounce. The reviewed hash includes that correction and the source's audit-hardening clarification.

This is an internal mathematical and computational review, not a novelty claim or external publication. It does not independently reprove the earlier mass-four classification, recheck the external literature, or establish binary/reversible versions of the examples.

## The local rules really define globally conservative CAs

For the planar rule, every changed site lies in the head-centered max-norm radius-two cube. Distinct eligible heads are more than four apart in max norm, so their radius-two write cubes are disjoint. This excludes conflicts even on malformed inputs with arbitrarily many heads, inactive heads, and extra units. Every original symbol at a write site is guarded, including the empty destinations, and each individual rewrite preserves its written-site weight. Thus their simultaneous union preserves total mass on every finite configuration.

A cell can be changed only by a head at distance at most two. Its output is determined by that candidate's write guards and radius-four isolation test, all visible inside the cell's radius-six neighborhood. The same construction is shift equivariant, fixes the vacuum, and fixes an isolated `u`. The alphabet has exactly one weight-one symbol and positive weights for both head states.

For the horizontal variant, the corrected right-bounce guard tests emptiness at `a+2e₁`. Without that explicit change, the tempting literal interpretation that retained the old guard could overwrite an extra unit and lose mass: `E` at `a`, `u` at `a+e₁`, `u` at `a+2e₁`, and an empty `a+2e₁+e₂` is a concrete witness. The corrected rule blocks this configuration, and the independent audit tests it. The left bounce only changes `W` to `E` in place when its neighbor is `u`, so it neither moves nor deletes that unit and needs no destination-vacancy test.

Embedding in three dimensions retains the same rewrite geometry while testing isolation in the full three-dimensional max norm. Heads on nearby different horizontal layers therefore block one another as specified; there is no untested transverse collision. Composing either CA with a unit shift preserves conservation, the alphabet hypotheses, and finite radius (at most seven for the shifted examples).

## Exact orbit and complete stationary site set

Write `l=k+n` and `h=t−Tₙ`, where `Tₙ=n²+(2k−3)n`. For the wedge CA, throughout the half-open cycle `0≤h<2(l−1)`:

- If `0≤h≤l−2`, the sites are `u` at `(0,n)` and `(l,n)`, and `E` at `(1+h,n)`
- If `l−1≤h≤2l−3`, put `j=h−(l−1)`; the sites are `u` at `(0,n)` and `(l+1,n+1)`, and `W` at `(l−1−j,n)`

The next transition gives precisely the next section. This verifies both the clock and the possible one-cycle-ahead marker. It also proves, without particle-time overcounting, that every row eventually contains exactly the visited coordinates `0,…,k+n`. There are no other sites. Thus

`S = {(x,y)∈Z² : y≥0, 0≤x≤k+y}`.

The stated centered-box polynomial follows by summing `min(N,k+y)+1` for `y=0,…,N`. Its leading coefficient is `1/2`, and the centered-square density is `1/8`. The containing rank and counting degree are genuinely two.

For the horizontal variant, replace both displayed row coordinates by zero. The ever-visited set is exactly the nonnegative horizontal ray, even though the gaps and the clock grow. Its spatial rank and degree are one; its time count grows as a square root.

## Distinct drifted trajectories and the floor formula

For the vertically shifted wedge, the left and head trajectories have equal height at each time and different horizontal coordinates. Their heights are strictly increasing, with a jump of two exactly at the left bounce. This gives the common skipped sequence

`aₙ = Tₙ+n−1 = n²+(2k−2)n−1`, for `n≥1`.

The right-marker trajectory has its sole per-cycle jump of two at the right bounce, whose completion time is `Tₙ+k+n−1`. Its skipped sequence is

`bₙ = Tₙ+k+2n−1 = n²+(2k−1)n+k−1`, for `n≥0`.

Strictly increasing height alone establishes no self-intersections within each trajectory; it does not establish mutual disjointness. The source supplies the needed additional argument. Before the right bounce, matching height with the head means the same time, when the right marker is strictly farther east. After that bounce, matching height can mean only the next head time, except at the last step of the cycle, where it is a skipped head height. The right marker then has coordinate `k+n+1`, and the next head coordinate is at most `k+n−1`. The left marker is always at horizontal coordinate zero. Hence all three *entire* trajectories are pairwise disjoint, including across different times.

Once the horizontal box constraint is inactive, each trajectory therefore contributes its number of attained heights, and the exact count is

`C_F(N) = 3(N+1)−2A(N)−B(N)`.

Solving `aₙ≤N` and `bₙ≤N`, with their different index ranges, gives exactly the displayed floor-root definitions of `A` and `B`. In particular, `A(N)=√N+O(1)` and `B(N)=√N+O(1)` for fixed `k`, so

`C_F(N)=3N−3√N+O(1)`.

The nonquasipolynomial conclusion is rigorous: an eventual quasipolynomial of order `N` with limit `C_F(N)/N=3` must have every constituent polynomial equal to `3N` plus a constant, giving a bounded residual. Here the residual tends to negative infinity. Semilinearity would imply eventual box quasipolynomiality, so this same full-set example is also nonsemilinear.

The source's threshold `N≥2k+4` is conservative. Its separately stated threshold `N≥k+1` is valid and is sharp for a threshold valid for every larger `N`. For the first newly moved right marker, `(x,height)=(k+1,k)`. Every later new right-marker coordinate `x=k+j`, `j≥2`, first occurs at height at least `x`. Every head point in cycles `n≥1` has height at least its horizontal coordinate, while cycle-zero head coordinates are at most `k−1`. Thus all horizontal coordinates are admitted when height≤N and `N≥k+1`. At `N=k`, exactly the point `(k+1,k)` is excluded horizontally but included by the height-only count, so the floor formula overcounts by one. This does not challenge either threshold actually used in the source.

## The separate nonsemilinear example

For the vertically shifted horizontal shuttle, every height `t` has exactly three visited sites. Their horizontal coordinates are uniformly `O(√t)`, but are unbounded. A period `(a,b)` in any linear component of a putative semilinear representation cannot have `b<0`, since no negative-height sites occur. If `b=0`, finiteness of each row forces `a=0`. If `b>0`, the uniform sublinear horizontal bound forces `a=0`. A finite union of such components would have only finitely many horizontal coordinates, a contradiction.

This argument applies to the full occupied-site union. It is not restricted to rare labels or section samples. Its box count is eventually `3(N+1)`, so the source is right to keep this argument separate from the nonquasipolynomial example.

## General frame restoration and linear box growth

The inherited stationary-frame phase positions are affine in the cycle and flight parameters. Restoring the drift adds `δ` times the quadratic section clock plus affine within-cycle time. This yields finite width in `span{E,ν,δ}` and does not preserve spatial Presburger definability automatically.

If `δ≠0`, every occupied position is `tδ+O(√t)`. One nonzero drift coordinate implies that any visit to the radius-`N` box happens by time `O(N)`, giving the linear upper bound because the mass-four input has at most four occupied sites at each time.

For the lower bound, a small multiple `T=⌊ηN⌋` places *all* support up to time `T` inside the box. Vacuum quiescence and locality give an occupied predecessor at bounded distance for any chosen occupied endpoint; iterating gives a path to time zero. Its drift-coordinate displacement is of order `N`. A path with bounded jumps spanning that displacement has linearly many distinct sites. This reasoning correctly avoids requiring identifiable particles or counting all time occurrences as distinct.

## Rank three is sharp even against finite unions of planar tubes

The section-point argument rules out one arbitrary bounded-width rank-two affine plane: a nonzero normal `ax+by+cz` bounded on `(0,n,Tₙ)` forces `b=c=0`, and boundedness on `(k+n,n,Tₙ)` then forces `a=0`.

That argument alone would not exclude a finite union of planes. The current source has the necessary stronger within-flight argument. The eastward head points are

`(1+j,n,Tₙ+j)`, for `0≤j≤k+n−2`.

On these, a fixed nonzero normal evaluates to

`c n² + (b+c(2k−3))n + (a+c)j + a`.

If `a+c≠0`, a bounded strip contains at most a fixed number of the integer `j` values per cycle, independent of `n`. If `a+c=0`, the remaining polynomial in `n` cannot be constant unless `a=b=c=0`; thus the strip misses every sufficiently late entire flight. A finite union of strips captures only `O(1)` of the `Θ(n)` flight points for large `n`. Every fixed-width affine plane is contained in such a strip, regardless of rationality. The stated stronger rank-three conclusion is therefore justified by the full orbit.

## Theorem B first arrival and time asymptotics

Given the complete affine phase/timing form, the relation “site `y` is visited in cycle `n` at offset `h`” is Presburger. Minimizing `n`, then `h`, uses only Presburger quantification and defines functions. The source's linear-set graph proof correctly shows that a single-valued Presburger function is rational affine on a finite semilinear partition: an integer relation among input generators must also hold among output generators, or functionality fails. Refining the two partitions yields affine `n_min(y)` and `h_min(y)` on each piece. Substitution into `T₀+c n_min²+b n_min+h_min` gives a rational polynomial of degree at most two. Earlier-prefix first visits are handled as finitely many singleton exceptions.

The lower bound `n_min(y)≥||y||/K−1` follows from the cycle support bound. The finitely many rational affine formulas give the upper bound `n_min(y)=O(||y||+1)`. The within-cycle duration is `O(n)`, so first arrival is uniformly `Θ(||y||²)` for escaping sites. To pass to box coverage time, the positive leading coefficient in the centered-box count ensures sites at radius at least a fixed positive fraction of `N`; otherwise counts at `N` and that smaller radius would contradict their asymptotics. This establishes `Θ(N²)` for this orbit's eventual box-site coverage.

Monotone complete-cycle counts have one positive rational leading coefficient. Their adjacent-cycle sandwich and `n(T)=√(T/c)+O(1)` yield the advertised `T^{r/2}` leading term with `O(T^{(r−1)/2})` error, including the rank-one `O(1)` endpoint case. Partial-cycle or section conventions alter only that lower-order error. No ordinary-time eventual quasipolynomiality follows.

For the concrete wedge the first-arrival function can be checked explicitly. At row zero, `τ(0,0)=τ(1,0)=τ(k,0)=0`, and `τ(x,0)=x−1` for `2≤x≤k−1`. For `y≥1`,

- `τ(0,y)=T_y`
- `τ(x,y)=T_y+x−1` for `1≤x≤k+y−1`
- `τ(k+y,y)=T_(y−1)+k+y−2`

This is a direct concrete realization of piecewise quadratic first arrival.

## Additional exact time formulas checked for the report

These supplemental identities were independently derived and tested; they do not alter the reviewed source packet.

For the wedge, let `Bₙ=n(n−1)/2+(k+1)n+3`. Then throughout cycle `n`,

`V(Tₙ+h)=Bₙ+min(h,k+n−2)+1_{h≥k+n−1}`,

for `0≤h<2(k+n−1)`. The outward head sweep adds one new site per move, the right bounce adds one new marker site, and the return sweep adds none. The next left bounce adds the two new section sites.

For the horizontal shuttle, after its initial sweep (`T≥k−2`),

`V(T)=floor(√(T+(k−1)(k−2)))+3`.

Indeed the new rightmost-site times are `Tₙ+k+n−1=(n+k−1)²−(k−1)(k−2)`, when the count becomes `k+n+2`. Consequently the first time `H(M)` at which at least `M` distinct sites have been seen is

`H(M)=(M−3)²−(k−1)(k−2)`, for `M≥k+2`.

The lower bounds on `T` and `M` matter; the initial sparse sites make extending the inverse formula earlier incorrect.

## Reproducible independent checks

`independent-audit.py` imports no source-packet code. It separately implements the transition rules and a cellwise evaluator using inverse write offsets and radius-six local reads. Its explicit `RuntimeError` guards remain active under `python -O`. Ordinary and optimized runs produce byte-identical JSON receipts.

The audit covers exhaustive noise-symbol choices at all six relevant guarded sites around a head, random malformed inputs in dimensions two and three, head-isolation boundaries, translation equivariance, full cycle states, exact stationary unions, actual cross-time drifted collisions, skipped-height sequences, all box radii through `N=8000` for five choices of `k`, and large-integer floor boundaries up to cycle index `10^12`. It also tests the concrete first-arrival formulas and the supplemental exact physical-time counts/inverse.

Finite checks are evidence against transcription, guard, endpoint, and counting mistakes. The disjoint-write, first-arrival, and strip arguments above are the unrestricted proofs; no finite simulation is presented as a replacement.
