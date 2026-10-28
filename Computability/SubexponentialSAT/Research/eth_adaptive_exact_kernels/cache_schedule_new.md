> Historical intermediate analysis: the closing five-packet intake supersedes some novelty and frontier claims below. These derivations remain valid supporting work, not the final headline. See report.tex, streamed_composition_new.md, late_cache_refinement.md, late_review_cauchy.md and fused_cauchy_new.md for the closing comparison.

# A new cached-table schedule: time below 38, space below 34

## Statement and provenance

Under the same normalized s-wire, maximum-degree ceil(s^0.9) interface and
unchanged upstream deformation/child identities, the following *new explicit
schedule* combines asymmetric balancing, slope-four full-orientation modes,
and the joint packet's cached three-block/Strassen algorithm. Its bounds are

`T <= poly(s+description) 2^((37.59170255554196...+o(1)) s/sqrt(log2 s))`,

`S <= poly(s+description) 2^((33.623040921657754...+o(1)) s/sqrt(log2 s))`.

Hence eventual coefficients 38 for time and 34 for space are valid. These
are tensor-normalized coefficients, not coefficients per SAT variable.
The same logarithmic exponent order remains. No global optimality claim
is made. It is an improvement over the explicit inherited combination
44.53757 time /39.49595 space, not a new matrix multiplication theorem.

## Schedule and packing

Let lambda=ceil(log2 s), b=ceil(6 log2 lambda), H=ceil(s/lambda).
For depths d=0,...,6 choose

|d|r_d|x_d|A_d=sum_(h<=d)x_h|
|-|-|-|-|
|0|7|89/5000|89/5000|
|1|9|13/1250|141/5000|
|2|8|29/10000|311/10000|
|3|6|1/500|331/10000|
|4|5|1/500|351/10000|
|5|4|1/500|371/10000|
|6|4|1/500|391/10000|

For d=7+j, use r_d=3 and x_d=(239/40000)(3/4)^j. The total sum is
63/1000. Put u_d=floor(lambda*x_d), a_d=sum_(h<=d)(u_h+b),
L_d=2^a_d and Q_d=r_d^a_d. Different calls can relabel with different
alphabets; this changes neither inherited parent entries nor the local
one-source/one-target property of the full-orientation modes.

Root packing needs `.9+2 A0 log2(r0)<1`. Below the root the retained side
has degree at most s^0.9 and the fresh side at most 2L_(d-1), so packing
needs `.9+A_d log2(r_d)<1`; remaining exponents are bounded by
`.2+.063=.263<1`. All principal margins have exact integer certificates
recorded by `code/verify_cache_schedule.py`, beginning `7^89<2^250` and
ending `3^63<2^100`.

The existing noncircular uniformity proof applies: first work at every
hypothetical depth up to ceil(log_(10/7) lambda)+10. In the geometric tail
u_d >= lambda^(1-ln(4/3)/ln(10/7)+o(1)), whose exponent is positive.
All floors are uniform relative o(1), all packing errors are uniform
O(1/lambda)+s^(-epsilon+o(1)), and child ratio is eventually at most .7.
An active path cannot reach this hypothetical depth limit, closing the
induction. More precisely

`M_d <= (1+o(1)) s m_d`, `m_0=1`, `m_(d+1)=2 m_d/r_d`.

Here m_7=1/1890 and tail masses multiply by 2/3. The additive guard gives
the existing uniform precision `p_t <= (6+o(1)) M D_i/u_d`; entry costs,
leaves, polynomial indexing, and O(log lambda) recursive levels are all
lower order on the s/sqrt(lambda) exponential scale. These details match
the separately proved adaptive polynomial-space schedule.

## Weighted pair entropy and complete cost

The exact pair inventory with unit padding gives the weighted entropy
scale `K_d=(pi sqrt(2)/ln2) M_d/sqrt(u_d)`. For a subset I of directed
group pairs, sum of logarithms of its exact-weight tuple list sizes is at
most `(sqrt(|I|/r_d^2)+o(1))K_d`. Weighted versions use sum of squared
weights. This is the joint packet's proved weighted entropy lemma with
the padded-volume constant reduced from three to one.

Partition the r groups as evenly as possible into three blocks with sizes
q1,q2,q3, and put v12=2q1q2, v13=2q1q3, v23=2q2q3. Let omega=log2(7):

* cache calls: `a(r)=sqrt(2(r-1))/r`;
* build block tables: `b_B(r)=max_q sqrt(2rq-q^2-q)/r`;
* Strassen contraction: `b_S(r)=sqrt(sum v-(1-(omega-2)^2) min v)/r`;
* boundary-table storage: `j(r)=max_q sqrt(2q(r-q))/r`.

Use c(r)=max(b_B,b_S). Exact weight allocations have polynomially many
possibilities because only a fixed finite set of alphabets occurs. Their
polynomial indexing and ring bit costs do not affect the coefficients.
The complete recursive cost has exponent bounded by

`max_d [sum_(h<d) a(r_h) K_h + c(r_d) K_d]`.

This explicitly pays for all child oracles. Table storage, including caches
and depth-first ancestors, has coefficient `max_d j(r_d) K_d`: all cache
indices are incident pairs, so a(r)<=j(r), and a sum of only polynomially
many tables takes the largest exponent, not their sum. The sequential-tape
or sorting realization already proved in the joint packet is unchanged.

For root r=7, block sizes are 2,2,3. Here b_B=sqrt(30)/7 exceeds b_S,
and j=sqrt(24)/7. Thus the candidate root coefficients are exactly

`C_T=(pi sqrt(2)/ln2) sqrt(30)/(7 sqrt(89/5000))`,

`C_S=(pi sqrt(2)/ln2) sqrt(24)/(7 sqrt(89/5000))`.

The recursive time coefficients at prefix depths are approximately

`37.591703, 37.560520, 37.565888, 37.037326, 37.069604, 37.158726, 37.224577`.

The complete tail is also smaller. With K7=(pi sqrt(2)/ln2)/(1890
sqrt(239/40000)) and gamma=(2/3)/sqrt(3/4)=4/(3sqrt3), the tail supremum is

`prefix_cache + K7 max(c(3), a(3)/(1-gamma)) = 37.324612...`.

Its storage is much smaller than the root. Therefore the root really
dominates both bounds, and the displayed exact expressions are valid.

## Exact verification and limits

`verify_cache_schedule.py` proves all comparison inequalities using exact
Fractions, integer powers and rational square-root enclosures. For the
Strassen coefficient it uses the verified upper bound omega<281/100;
for the eventual rounded bounds it uses pi<22/7 and ln2>6931/10000,
the latter checked from four positive series terms. No floating-point
comparison decides a certificate. Results are in
`results/cache_schedule_checks.json`.

The small strict packing gaps make this an asymptotic certificate, not a
practical threshold estimate. It is not polynomial space. Its use of
existing ingredients is explicitly credited; the new contribution here
is this adaptive cached-table schedule, separately from the new quadratic
Cauchy feature-table implementation in `cauchy_review.md`.
