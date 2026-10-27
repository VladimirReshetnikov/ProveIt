# A proved Hermite precision refinement

**Status:** this note proves a refinement of the source algorithm's interpolation parameters and of its explicit exponential upper-bound constant. It does not improve the order `M/sqrt(log s)` of that bound, and it supplies no lower bound on the old algorithm's actual running time.

**Source:** OpenAI `math` commit `42907c9e999cc00d6abe7a50bfc1023250edd1b9`, `quantitative-contraction.tex`, especially the tapered Hermite recovery and mode-counting arguments.

## 1. Exact multiplicity for a linear taper

Let `L=2^a`, `a>=u>=1`, and let the multiplicity at every node of valuation `i<u` be

`q_i=h(u-i)`.

There are exactly `L/2^i` nonzero grid nodes of valuation `i`, for `0<=i<a`. Therefore the total multiplicity is

`Q=L h sum_{i=0}^{u-1}(u-i)2^{-i}`

` =L h (2u-2+2^{1-u})`.

Since the polynomial degree is at most `M(2L-1)`, the least positive integer linear-taper slope guaranteeing ordinary Hermite completeness is

`h_min=ceil((M(2L-1)+1)/(L(2u-2+2^{1-u})))`.

The denominator is an integer because `a>=u`. In the source regime `u` tends to infinity and `M/u` tends to infinity, so

`h_min=(1+o(1)) M/u`.

This replaces the source's sufficient choice `h=ceil(3M/u)`. All retained levels remain active, so the packet/locality construction is unchanged. The source's auxiliary bounds `h<=4M/u` and `q_i<=4M` continue to hold for sufficiently large admissible sizes.

## 2. Exact sufficient precision

For `i=v_2(t)<u`, put `D=2^{a-i}` and define

`B_i=D sum_{j=1}^{a-i} j 2^{-j}(q_i-q_{i+j})`,

where `q_j=0` for `j>=u`. The source's exact valuation identity gives

`B_i=-v_2(E_t(0))`.

For a nonincreasing nonnegative taper, `B_i>=0`. The reciprocal series `1/E_t(t+alpha z)` is integral, with `alpha=2^{a+1}`, so forming the required quotient jet loses no precision. Its `j`th coefficient is multiplied, during recovery, by

`E_t(0)(-t/alpha)^j`,

whose valuation is exactly

`-B_i-j(a+1-i)`.

For `0<=j<q_i`, the worst loss is therefore

`B_i+(q_i-1)(a+1-i)`.

Consequently the following precision is sufficient, without the source's slack constants:

`p'_t=p+B_i+(q_i-1)(a+1-i)`.

Every coefficient error is then sent into `2^p A`, and summing the errors loses no further precision. This argument applies coordinatewise in the same truncated coefficient ring as the source.

For a possibly nonmonotone taper, the uniformly safe version is

`p'_t=p+max(0,B_i+(q_i-1)(a+1-i))`.

This also ensures that recursive precision never decreases. For the positive linear taper above, `B_i>0`, so precision strictly increases as in the source.

## 3. Leading precision constant

For the linear taper, with `k=u-i`, the full infinite-grid normalized loss is exactly

`sum_{j>=1} j2^{-j}(q_i-q_{i+j})`

` =h(6-2^{1-k}(k+3)) <=6h`.

The actual finite-grid loss is no larger. Thus `B_i<=6hD`. The other terms satisfy, uniformly over the source's active calls and active interpolation levels,

`p=o(MD/u)` and `(q_i-1)(a+1-i)=o(MD/u)`.

These follow from the source's cumulative packet length and the bound `D>=2^{a_{d-1}+u}`, because `u` is a positive power of `log s` at every active depth. Hence the refined linear taper and exact precision give

`p'_t <= (6+o(1)) MD/u`.

By comparison, the source's precision prescription is

`p_t=p+8 ceil(3M/u)D+8M(a+1)`

`   =(24+o(1))MD/u`

uniformly in the same regime. The refined bound is an inequality: levels near the end of the taper have normalized loss strictly below the leading constant `6`.

## 4. Explicit colored-partition constants

There are at most `6M/D` mode variables of any given positive integer weight. For any `theta>0`, their feasible exponent tuples satisfy

`ln N <= theta P + (6M/D) sum_{j>=1}[-ln(1-exp(-theta j))]`.

Using the standard expansion of the logarithm,

`sum_{j>=1}[-ln(1-exp(-theta j))] <= pi^2/(6theta)`.

Therefore

`ln N <= theta P + pi^2 M/(D theta)`.

The optimizing choice is `theta=pi sqrt(M/(DP))`, giving

`ln N <=2pi sqrt(MP/D)`.

For the source precision this yields

`ln N <=(4pi sqrt(6)+o(1)) M/sqrt(u)`;

for the refined precision it yields

`ln N <=(2pi sqrt(6)+o(1)) M/sqrt(u)`.

Thus the dominant constant in this certified enumeration upper bound is halved. This is a comparison of two proved upper-bound derivations, not a proof that an implementation always runs twice as fast, nor that the old bound is attained.

## 5. Explicit global recurrence bound

Assume the root has at most `s` wires. Keep the source leaf threshold `H=ceil(s/floor(sqrt(lambda)))`, with `lambda=ceil(log_2 s)`, and keep `epsilon=1/(128*1024)`. Since `M_d<=s8^{-d}` and `u_d=(1+o(1))epsilon lambda 2^{-d}` uniformly over active depths,

`sum_d M_d/sqrt(u_d)`

` <=(1+o(1)) [s/sqrt(lambda)]/[sqrt(epsilon)(1-sqrt(2)/8)]`.

Polynomial branching costs contribute only `O(lambda log lambda)`, and entry evaluation contributes `O(s^{9/10})`; both are `o(s/sqrt(lambda))`. Direct leaf enumeration contributes `(ln 2+o(1))s/sqrt(lambda)`.

Consequently the refined algorithm has the explicit bound

`T <= (s+description_length)^{O(1)}`

`     * exp( [2pi sqrt(6)/(sqrt(epsilon)(1-sqrt(2)/8)) + ln 2 + o(1)] s/sqrt(lambda) )`.

The same calculation for the source's precision has `4pi sqrt(6)` in place of `2pi sqrt(6)`. If the root only satisfies `M_0<=C s`, insert the corresponding fixed factor in the geometric-sum term, or normalize the root size parameter first. One can modestly sharpen the geometric factor by using the actual child bound `3M/32`; the displayed statement deliberately keeps the source's simpler `M/8` invariant.

## 6. Optimal real taper for the full loss functional

The optimized linear taper is asymptotically optimal in leading constant within this retained-level Hermite loss model. This can be proved exactly, rather than inferred from a slope heuristic.

Fix an allowable maximum full normalized loss `H`. The loss constraints are equivalent to

`q_i <= H/2 + sum_{j>=1}[j/2^{j+1}]q_{i+j}`,

with `q_i=0` for `i>=u`. The pointwise maximal feasible vector saturates these inequalities, by backward induction. Set `k=u-i` and write `q_i=H r_k`. Then

`r_k=1/2+sum_{j=1}^{k-1}[j/2^{j+1}]r_{k-j}`.

Its generating function is

`R(z)=sum_{k>=1}r_k z^k=z(2-z)^2/[2(1-z)^2(4-z)]`.

Partial fractions give

`R(z)=-1/2 + 1/[6(1-z)^2] + 1/[9(1-z)] + 8/[9(4-z)]`,

so, for `k>=1`,

`r_k=k/6+5/18+(2/9)4^{-k}`.

Thus the largest achievable weighted multiplicity at loss `H` is

`W_max(H)=sum_{i=0}^{u-1}2^{-i}q_i`

`        =H[u/3+2/9-(2/9)4^{-u}]`.

For a required weighted multiplicity `W`, the exact optimal real full-loss value is

`H_opt=W/[u/3+2/9-(2/9)4^{-u}]`.

Hermite completeness requires `W=2M+o(M)`, giving

`H_opt=(6+o(1))M/u`.

The refined linear taper already attains this leading constant. Choosing the exact real taper instead only changes lower-order terms.

### Finite-grid and integer refinements

The finite-grid optimum is also a triangular recurrence. With

`S_i=sum_{j=1}^{a-i}j2^{-j}=2-(a-i+2)2^{-(a-i)}`,

set, backwards in `i`,

`q_i=[H+sum_{j=1}^{u-1-i}j2^{-j}q_{i+j}]/S_i`.

Because each `S_i>0`, this saturating vector pointwise dominates every vector with finite normalized losses at most `H`, and hence maximizes the weighted multiplicity. The recurrence has rational coefficients of polynomial bit length and is directly computable.

After scaling the real optimum to meet the required weighted multiplicity, round each `q_i` upward to an integer. The weighted multiplicity only increases. Every normalized loss increases by less than `2`, because its diagonal coefficient is at most `2` and all off-diagonal coefficients are nonpositive. Thus integer rounding preserves the leading constant. These refinements are optional; the simple integer `h_min` formula already proves the global constant improvement above.
