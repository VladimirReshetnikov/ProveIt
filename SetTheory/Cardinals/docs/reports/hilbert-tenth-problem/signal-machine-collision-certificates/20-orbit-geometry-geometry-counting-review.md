# Distinct-site counting review for an expanding shuttle

Independent review, 3 October 2026. All sets below are sets of **distinct sites**, not multisets of parameter witnesses. The results concern the reference frame in which the stated affine spatial normal form holds. Restoring a time-dependent translation such as `δt` is a different problem and does not preserve these assertions automatically.

## 1. Precise hypotheses and notation

After a finite prefix, suppose the positions visited in cycle `n ≥ 0` are a finite union of phase sets

    y = o + n(E + εΔν) + jmν,
    n in a specified fixed residue class,
    0 ≤ j ≤ an+b,

with rational fixed coefficients, `ν ≠ 0` an integer vector on a rational line, `E ∈ Z^d`, `Δ > 0`, `m ≠ 0`, and `a > 0`. Only integer parameters producing the designated integer positions are retained; denominators can be cleared. Each specified residue class is nonempty and infinite. There is at least one such genuine growing phase. Finite marker/local-prefix lists have positions affine in `n`. In the shuttle construction their slopes also belong to `span_Q(E,ν)`, although the counting degree conclusions below remain valid if these finitely many extra affine lists have arbitrary slopes.

Write

    r = dim_Q span_Q(E,ν) ∈ {1,2},
    S = the union of all visited sites, including the finite prefix,
    C(N) = #(S ∩ [-N,N]^d),
    S_<K = sites visited in the prefix and cycles 0,...,K−1,
    D(K) = #S_<K.

For exact formulas, assign cycle `n` the half-open time interval `[T_n,T_(n+1))`; any phase-boundary duplicates can be assigned to the latter cycle by affine inequalities. For statements using exact time, assume the normal form records, for every phase occurrence, its actual time offset within its cycle:

    h = h_phase(n,j),

an affine rational expression integral on its domain. Local-prefix offsets are affine in `n`. Assume cycle start times are

    T_n = T_0 + c n² + b n,    c > 0,

and these are strictly increasing. This is exactly the form obtained from the shuttle's affine cycle durations, with `c=A/2` in the proof packet's notation. Denote by `V(T)` the number of distinct sites visited by integer time `T`.

If only `T_n ~ c n²` is known, the leading time asymptotic below still follows, but its stated error term requires `T_n = c n² + O(n)`.

## 2. Effective Presburger, semilinear, and generating-function conclusions

Membership in `S` is the finite disjunction over phases of

    exists n,j: phase-domain(n,j) and y=o+n(E+εΔν)+jmν,

plus the affine marker lists and finite prefix. All conditions are Presburger after clearing denominators. In particular `S` is effectively semilinear. Crucially, the quantified witnesses `n,j,phase` are not counted: the free counted variable is the site `y` itself.

An effective disjoint semilinear decomposition, or Presburger quantifier elimination followed by polyhedral/congruence decomposition, gives rational generating functions for the characteristic function of `S`. For a genuinely signed subset of `Z^d`, state this orthant by orthant, or use the injective nonnegative encoding

    y ↦ (y_1^+,y_1^−,...,y_d^+,y_d^−).

Do not regard an unrestricted bilateral sum `sum_{y in S} z^y` as an ordinary formal power series: opposite infinite directions need a specified expansion convention and may not have a common analytic domain of convergence. The nonnegative encoding avoids this issue completely.

The following finite-fiber families are also Presburger:

- `y ∈ S` and `−N_i ≤ y_i ≤ N_i` for all `i`
- `y ∈ S_<K`
- Their combination, with parameters `(K,N_1,...,N_d)`
- Sites visited in previous cycles or by offset `s` in cycle `n`

Consequently their counting functions are effectively piecewise quasipolynomial and have rational multivariate parameter generating functions. In one nonnegative parameter, a finite polyhedral partition reduces to finitely many exceptional intervals and one unbounded interval, so the counting function is eventually quasipolynomial.

**Primary source checked:** Kevin Woods, *Presburger arithmetic, rational generating functions, and quasi-polynomials*, Journal of Symbolic Logic 80 (2015), 433–449, DOI [10.1017/jsl.2015.4](https://doi.org/10.1017/jsl.2015.4), [author's arXiv version](https://arxiv.org/pdf/1211.0020). Theorem 1.5 identifies Presburger sets with polyhedral/lattice-coset descriptions and rational characteristic generating functions. Definition 1.9 specifies the finite-polyhedral meaning of piecewise quasipolynomial. Theorem 1.10 gives Presburger counting ⇒ piecewise quasipolynomial ⇔ rational generating function. Theorem 3.2 and §4.1 give the quantifier-elimination construction. These are effective existence results here; no polynomial-time claim is being made.

## 3. Centered cubes: the degree is exactly r

### Theorem

There is an effectively computable eventual quasipolynomial `C(N)` of degree exactly `r`, and a computable rational constant `κ > 0`, such that

    C(N) = κN^r + O(N^(r−1)).

Every eventual residue polynomial has degree `r` and has the same leading coefficient `κ`. Thus the ordinary generating function `sum_N C(N)z^N` is rational; for some effective period `M`, it can be expressed with denominator dividing `(1−z^M)^(r+1)`, after including a finite-prefix polynomial.

### Proof of the upper bound

Every growing phase lies in a fixed translate of the rational vector space `span_Q(E,ν)`. A finite union of fixed rational affine `r`-flats contains `O(N^r)` lattice sites in the cube. This follows, for example, by choosing `r` coordinate projections injective on each flat; each coordinate ranges over `2N+1` possibilities. The finite affine marker lists contribute `O(N)` each, even if their slopes were not assumed to lie in that vector space. Therefore `C(N)=O(N^r)`.

### Proof of the lower bound when r=2

Fix one growing phase and write `P=E+εΔν`. Since `E` and `ν` are independent, so are `P` and `mν`; the map `(n,j)↦o+nP+jmν` is injective within this one phase. Choose a sufficiently small fixed positive `η`. For all admissible residue-class `n` between a fixed threshold and `ηN`, all `j` with `0≤j≤an+b` produce points in `[-N,N]^d`. There are `Ω(N²)` such pairs, giving `C(N)=Ω(N²)`.

### Proof of the lower bound when r=1

It is incorrect to use injectivity in `(n,j)` here. Instead, choose just one admissible cycle number `n` within `O(1)` of `ηN`, with `η>0` sufficiently small. That phase's `Ω(N)` values of `j` all lie in the cube and give distinct sites because `mν≠0`. Thus `C(N)=Ω(N)` despite arbitrary intercycle collisions.

The Presburger theorem already gives an eventual quasipolynomial. The upper and lower bounds force degree exactly `r` on every eventual residue class. Finally, `C(N)` is nondecreasing. If its leading coefficients on consecutive residues modulo `M` are `κ_0,...,κ_(M−1)`, monotonicity gives

    κ_0 ≤ κ_1 ≤ ... ≤ κ_(M−1) ≤ κ_0.

Hence they are all the same positive rational number. This proves the theorem without any unjustified density or injectivity assumption.

## 4. Multibox and anisotropic caveats

The function

    C(N_1,...,N_d) = #(S ∩ product_i [−N_i,N_i])

is effectively piecewise quasipolynomial on finitely many rational polyhedral parameter pieces, with residue-dependent polynomials on each piece. It need not be one global quasipolynomial. Offset vectors can make the chambers affine polyhedra rather than cones. Chamber boundaries and lower-dimensional parameter pieces must be included.

For the valid rank-two phase set

    S = {(n,j): n≥0, 0≤j≤n},

one has

    C(N_1,N_2) = (N_1+1)(N_1+2)/2                 if N_1≤N_2,
    C(N_1,N_2) = (N_2+1)(N_2+2)/2
                 +(N_1−N_2)(N_2+1)             if N_1≥N_2.

The chamber change is real. Along `N_2=0`, the degree drops to one. More general translated boxes can be empty or miss every unbounded component. Therefore “degree exactly r everywhere in multibox parameter space” is false.

Along any fixed rational dilation with every side length proportional to a strictly positive constant, the one-parameter result again has sharp degree `r` (after treating floors via residue classes). Zero side-length slopes can lower the degree or remove an unbounded component.

## 5. Counts through complete cycles

### Theorem

`D(K)` is an effectively computable eventual quasipolynomial, and there is a computable `α ∈ Q_{>0}` such that

    D(K) = αK^r + O(K^(r−1)).

### Proof

Presburger definability follows by adding `0≤n<K` under the existential site-membership formula. In rank two, the fixed injective growing phase gives `Ω(K²)` sites. In rank one, a single phase with `n` within a bounded distance of `K−1` gives `Ω(K)` distinct sites.

All positions in cycles `<K` have norm `O(K)` and lie in a finite union of the previously described flats/rays, so the matching upper bound is `O(K^r)`. Monotonicity of `D(K)` forces the common leading coefficient exactly as in §3.

In particular,

    D(K+1)−D(K) = O(K^(r−1)).

For rank one, this says that **the number of genuinely new sites in an entire late cycle is uniformly bounded**, even though a shuttle traverses `Θ(K)` positions in that cycle. This conclusion counts distinct sites and is not a claim about how many visits occur.

## 6. Physical-time counts in the stated reference frame

Let `n(T)` be the unique cycle index satisfying `T_n≤T<T_(n+1)`. Apart from harmless boundary conventions for sites at cycle start/end,

    D(n(T)) ≤ V(T) ≤ D(n(T)+1).

The exact quadratic inversion is, for sufficiently large `T`,

    n(T) = floor((−b + sqrt(b²+4c(T−T_0)))/(2c)).

Therefore

    V(T) = α c^(−r/2) T^(r/2) + O(T^((r−1)/2)).

Specifically:

- Rank one: `V(T) = (α/√c)√T + O(1)`
- Rank two: `V(T) = (α/c)T + O(√T)`

These leading constants are effective. The rank-two one is rational; the rank-one one is algebraic of degree at most two. With only `T_n~cn²`, replace the displayed error assertion by the corresponding asymptotic equivalence.

### Exact representation without simulating every time

Define `Q(n,s)` as the number of sites in the finite prefix, earlier cycles, or phase occurrences in cycle `n` with affine time offset at most `s`. This is a finite-fiber Presburger count in `(n,s)`, so it has an effective piecewise-quasipolynomial description. Hence

    V(T) = Q(n(T), T−T_(n(T)))

is an exact effective eventual formula involving a quadratic floor root and a piecewise quasipolynomial. This is more informative than incorrectly asserting quasipolynomiality directly in `T`.

### Why time counts need not be quasipolynomial or rational-generating

Consider the valid rank-one abstract shuttle schedule whose cycle `n≥1` visits the positions

    0,1,...,n,n−1,...,1

at `2n` successive times. Then `E=0`, `ν=1`, `Δ=1`; its two flights have the required affine-in-`(n,j)` form and cycle starts `T_n=n(n−1)`. Site `n` is first reached at time `n²`, so exactly `V(T)=floor(√T)+1`. An unbounded eventual quasipolynomial cannot have sublinear square-root growth, so `V(T)` is not eventually quasipolynomial.

Its first difference is a bounded integer sequence with arbitrarily long zero blocks and infinitely many nonzero terms, and is not eventually periodic. If the generating function of `V(T)` were rational, its first-difference sequence would satisfy a fixed rational linear recurrence. A bounded integer recurrence sequence is eventually periodic: the finite tuples of consecutive terms form a finite state space and the recurrence determines the next term. This is a contradiction.

The example establishes what does not follow from this normal form alone; it is not asserted here to be a separately constructed CA realization. Rank-two schedules can likewise have growing blocks of new-site discovery alternating with repeated-site sweeps, so even a positive linear leading term does not guarantee eventual quasipolynomiality.

## 7. Effective spatial inverses

Let

    R(k) = min{N≥0: C(N)≥k}.

Then

    R(k) = (k/κ)^(1/r) + O(1).

To prove this, use the uniform bound `|C(N)−κN^r|≤B N^(r−1)` and compare with `(k/κ)^(1/r)±L`, for a sufficiently large fixed `L`. The same proof applies to the inverse completed-cycle count `min{K:D(K)≥k}` with `α` in place of `κ`.

This inverse is exactly effective: on each eventual residue class `N=u+Mq`, substitute into the degree-`r` polynomial for `C`. Solve its eventually increasing linear or quadratic inequality against `k`; take the minimum over the finite residues and finite exceptional values. Thus it is a finite minimum of rational affine ceiling formulas if `r=1`, or quadratic-root ceiling formulas if `r=2`.

For `r=1`, `R(k)` is eventually quasi-affine. For `r=2`, it cannot be eventually quasipolynomial, since it is unbounded and has growth `Θ(√k)`.

For the first time at which `k` distinct sites have been visited,

    H(k) = min{T:V(T)≥k},

the preceding time estimate implies

    H(k) = (c/α²) k² + O(k)                  if r=1,
    H(k) = (c/α) k + O(√k)                  if r=2.

## 8. Site-specific first-visit times are piecewise quadratic

Under the affine within-cycle timing hypothesis of §1, define for a visited site `y`:

- `n_*(y)`: the earliest cycle containing `y`
- `h_*(y)`: the earliest time offset at which `y` occurs in that cycle

Treat first visits in the initial finite prefix separately. Both graphs are Presburger: quantify the relevant occurrence, then exclude any smaller cycle and any smaller offset within the selected cycle. Consequently both are effectively piecewise rational affine on finitely many semilinear domain pieces.

Here is an elementary justification of that last standard fact. Decompose the graph of a Presburger function into finitely many linear sets. On one such graph component, write the generator vectors as `(v_i,w_i)`, with `v_i` in the input coordinates and `w_i` in the output coordinates. Every integer linear relation among the `v_i` must also hold among the `w_i`: separate its positive and negative parts to obtain two points of the graph with the same input, and use functionality. Therefore the assignment `v_i↦w_i` extends to a rational linear map on their rational span. The function is affine on that component. Quantifier elimination refines its semilinear domain into polyhedral/congruence pieces if desired. This is effective and extends to several output coordinates.

It follows that the absolute first-visit function is

    τ(y) = T_0 + c n_*(y)² + b n_*(y) + h_*(y),

which is an effective rational polynomial of degree at most two on each of finitely many semilinear cells. Thus it is piecewise quadratic with congruence conditions, although the space-time orbit itself need not be Presburger.

Moreover, there exist positive effective constants `a_0,a_1` and a radius threshold such that every visited site outside that threshold obeys

    a_0 ||y||_∞² ≤ τ(y) ≤ a_1 ||y||_∞².

The lower bound uses `||y||≤K_0+K_1n` throughout cycle `n` and quadratic section times. The upper bound uses piecewise affineness of `n_*(y)` and `h_*(y)`: finitely many rational affine formulas give `n_*(y),h_*(y)=O(||y||+1)`.

This conclusion requires the actual affine time offsets, not merely the unordered spatial union and a rough estimate for cycle start times.

## 9. A stronger inverse theorem in rank one

With the same exact phase timing, rank one additionally implies:

    H(k) is an effective eventual quasipolynomial of degree exactly two,
    with common leading coefficient c/α².

Proof: by §5, at most a fixed number `M` of genuinely new sites are discovered in any sufficiently late cycle. The eventual graph of `D(n)` is Presburger because `D(n)` is quasi-affine. For each fixed `ℓ≤M`, the assertion “at least `ℓ` sites new in cycle `n` have appeared by offset `s`” is Presburger, witnessed by `ℓ` pairwise distinct sites, with nonappearance in earlier cycles imposed by negation. A finite disjunction over `ℓ` therefore defines the earliest cycle `n(k)` and the earliest offset `s(k)` at which the total distinct-site count reaches `k`. These are Presburger functions of `k`, hence eventually quasi-affine. Substituting them in

    H(k)=T_0+c n(k)²+b n(k)+s(k)

gives eventual quasipolynomiality of degree two; the leading coefficient follows from §7.

As a corollary, rank-one `V(T)` admits an eventual exact description as a finite maximum of floor-quadratic-root formulas: solve the eventual quadratic formula for `H(k)` on each residue class and take the largest admissible `k`. This still does not make `V(T)` quasipolynomial in `T`.

## 10. Audit cautions

1. Count sites as free variables, with phase/cycle parameters existentially quantified. Summing the sizes of phase parameter domains is wrong whenever images overlap.
2. In rank one, use a fixed late cycle to establish the lower bound; do not claim `(n,j)` injectivity.
3. Distinguish eventual quasipolynomiality in spatial box radius or cycle number from the square-root clock substitution in physical time.
4. Multibox counts are piecewise quasipolynomial, with possible degree loss on degenerate parameter directions.
5. The fixed-reference-frame assumption is essential. The normalization in the source proof is `G=τ_(−δ)F`; the physical-frame support of `F` adds `δt`, a quadratic contribution in cycle number.
6. All statements are fixed-input effective constructions. They assert neither small output size nor favorable complexity.
