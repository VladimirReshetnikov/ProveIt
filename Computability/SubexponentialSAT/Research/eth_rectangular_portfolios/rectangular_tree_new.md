# Rectangular support portfolios: new combined cached certificate

> Closing refinement: `four_plan_portfolio_new.md` strengthens the cached headline to **30.491276185937… time /28.853020941407… space**, with safe eventual coefficients **30.492 /28.854**, on the same retuned schedule. The three-plan results below remain valid intermediate comparisons and proof dependencies.

## Result and provenance

Under the normalized generic exact-contraction interface shared by the incoming packets (maximum degree `ceil(s^.9)`, polynomial description, precision/truncation at most O(s), admissible original entry routines and immutable creation-precision conventions), there is a deterministic relative-interface contraction algorithm with

`T ≤ poly(s+L) 2^{(30.614393627106…+o(1)) s/sqrt(ceil(log2 s))}`,

`S ≤ poly(s+L) 2^{(29.966734873162…+o(1)) s/sqrt(ceil(log2 s))}`.

Thus **30.615 time /29.967 space** are safe eventual coefficients. Space is subexponential. The SAT logarithmic order is unchanged. The normalized per-wire constants cannot be substituted for SAT-variable constants without an encoder analysis.

The ingredients are credited to `subsat_rectangular_2026-10-26` (genuine rectangular cost, coefficient-ring bridge) and `sat_adaptive_tree_certificate_2026-10-26` (three-plan menus, finite support averaging, paid recurrence, `9→13→7` schedule architecture). This iteration supplies the combined explicit support certificate and a small rational schedule retuning. On the **unchanged inherited schedule**, the combination already gives **30.629497100307… time /29.985755335168… space**. This matched ablation isolates the gain due to combination rather than schedule adjustment.

The strongest comparable supplied general-degree cached pair was **30.891018920366… /30.753912832055…**. Both coordinates improve. Existing low-degree or polynomial-space branches remain separate applicable options. No all-algorithm optimality or measured runtime advantage is claimed.

## 1. Rectangular cost as a finite support set

Fix `epsilon=1/100000`, and write

`d=1+epsilon/2=1400007/1400000`,

`v=47/56+epsilon=1175014/1400000`,

`w=15/28=750000/1400000`.

The imported exact rectangular algorithm has bit cost, up to a polynomial factor in the normalized input parameters,

`2^{F(x,y,z)}`, where for sorted logarithmic dimensions `x≥y≥z≥0`,

`F(x,y,z)=max{d(x+y), x+v y+w z}`.

The input/output term is retained. Since `1≥v≥w≥0`, rearrangement shows that for arbitrary unordered dimension logs `(H1,H2,H3)`, this is the maximum of the nine linear forms obtained from permutations of `(d,d,0)` and `(1,v,w)`. The first family has three distinct permutations; the second has six.

For a merge of disjoint vertex subsets A,B with complement O, the three dimension classes are undirected edges A–B, A–O, B–O. For a final triangle, they are the three block-pair edge classes. An edge internal to one part has coefficient zero. Let `L0=1400000`; multiplying all support coefficients by L0 gives **integer** vectors. The two coefficient multisets are

`(1400007,1400007,0)` and `(1400000,1175014,750000)`.

This representation is exact for the quoted cost bound, not an approximation from floating logs.

The field assumptions are only `alpha>.3` and `omega<19/8` (cited in the incoming report to arXiv:2307.07970). As in that report, fix finite rational bilinear algorithms, use fixed tensor products and constant-factor padding, omit finitely many denominator primes, and perform coordinate products over enough odd primes to reconstruct the positive integer products before reducing in the actual ring. The actual ring need not be a field and can contain nilpotents. The free-module rank, coordinate precision, and reconstruction bit bounds are polynomial. Workspace is a polynomial factor times the largest input/output array. These are inherited technical dependencies, not newly proved field algorithms.

## 2. The same three plan menus

A plan first builds each listed final block by recursively splitting its ordered list after `floor(k/2)` elements, then contracts the three block tables. There are r−3 binary merges plus one final triangle. Group labels start at zero.

For r=9:

1. `(0,1,2) | (3,4,5) | (6,7,8)`
2. `(6,2,5) | (4,7,0) | (1,8,3)`
3. `(5,2,8) | (4,6,1) | (0,7,3)`

For r=13:

1. `(0,1,2,3,4) | (5,6,7,8) | (9,10,11,12)`
2. `(12,10,1,6,4) | (9,0,3,8) | (5,2,7,11)`
3. `(0,8,11,12,1) | (7,10,4,3) | (5,2,6,9)`

These plans are unchanged from the incoming tree-certificate packet. For each plan j let V_j be the set of all nine integer support forms for all its operations, deduplicated. Let g_e=h_ab+h_ba be the sum of the two directed list logarithms on undirected edge e. The plan cost is

`F_j(g)=(1/L0) max_(v∈V_j) v·g`.

Choose the plan minimizing this complete operation cost. It includes block construction, not merely the final triangle.

## 3. Exact finite certificate and proof

For each r define

`Q_r=max_(v_j∈V_j,j=1,2,3) ||v1+v2+v3||₂²`.

The new exhaustive integer calculation gives:

|r|supports per plan|triples enumerated|Q_r|sum of all squared norms|
|---:|---:|---:|---:|---:|
|9|57|185193|246255154308036|24785168341806412920|
|13|89|704969|519754477218816|144283691430119248320|

Every tuple is checked using exact unbounded integers. The standard-library verifier reconstructs support vectors from the above vertex plans; it does not read generated masks as trusted inputs or execute any incoming code. The sum column and a coordinate-reconstructed attaining witness are auxiliary reproducibility checks. A separately authored NumPy implementation initially obtained the same maxima. Normal Python and `python -O` runs agree; no check depends on `assert`.

**Finite support lemma.** The minimum plan cost is bounded by `(b_r+o(1))K`, with

`b_r²=2 Q_r/(9r²L0²)`.

**Proof.** For nonnegative g,

`min_j F_j(g) ≤ (1/3) Σ_j F_j(g)`

`= (1/(3L0)) max_(v1,v2,v3) (v1+v2+v3)·g`.

For a fixed support tuple, put the same coefficient `(v1+v2+v3)_e/(3L0)` on each of the two orientations of edge e. Its directed squared norm is at most `2Q_r/(9L0²)`. The inherited weighted-entropy estimate says that a fixed coefficient vector z obeys

`Σ_e z_e h_e≤(||z||₂/r+o(1))K`, where `K=πsqrt(2)M/(ln(2)sqrt(u))`.

Apply it to all finitely many fixed support sums and take their common maximum error. This gives the claimed bound uniformly over every feasible exact-weight array. It neither exchanges min and max nor assumes arbitrary edge permutations arise from vertex relabelings. ∎

Thus

`b9²=2280140317667/6615000000000`, `b9=.587105113124937…`,

`b13²=24170130079/69316406250`, `b13=.590502138389288…`.

The dimensions are exact integer products of exact mode-list sizes. A plan can be chosen without real arithmetic by comparing products raised to the fixed nonnegative integer support powers. Although these exponents are large constants, all resulting bit lengths are polynomial. Alternatively use ceiling binary logarithms; there are constantly many coordinates and the coefficients are fixed, so this changes every cost by O(1), which preserves the leading certificate.

Every intermediate table is an input or output of an operation. The output branch `d(x+y)` is at least every pairwise dimension sum, because x,y are the two largest logs and d>1. Hence all stored arrays, including singleton caches, have local storage coefficient at most b_r. The fast backend's workspace is bounded by the same envelope up to polynomial factors.

## 4. The fully paid recurrence

Caching singleton group functions requires real recursive child contractions, not free oracle calls. The incident-pair entropy coefficient is unchanged:

`alpha_r=sqrt(2(r−1))/r`.

For r=9,13 use the rectangular support-portfolio algorithm. In the tail r=7 keep the inherited fixed square-backend plan, with

`b7²=632/1225`.

This is deliberately a hybrid: no new tail certificate is required. The local paid time recurrence is

`T_d ≤ poly(s)[2^{(alpha_(r_d)+o(1))K_d} T_(d+1) +2^{(b_(r_d)+o(1))K_d}]`.

Local storage is at most `poly(s)2^{(b_(r_d)+o(1))K_d}`. Ancestor tables add their storage sizes, not their exponents. Entry descriptions keep the inherited immutable-creation convention. The polynomial dependence on the original description length is not re-exponentiated across recursion levels.

## 5. Strict rational retuned schedule

Let `lambda=ceil(log2 s)`, `B=ceil(6log2 lambda)` and `H=ceil(s/lambda^(3/4))`. Stop at H and use direct contraction below it. Set

`r0=9`, `r1=13`, `r_d=7 for d≥2`,

`f0=1577/100000`, `f1=2813/250000`,

`f_d=(1433/300000)(4/9)^(d−2) for d≥2`,

`u_d=floor(f_d lambda)`, `a_d=Σ_(j≤d)(u_j+B)`.

The exact cumulative leading fractions are

`A1=f0+f1=13511/500000`,

`Ainf=f0+f1+(9/5)f2=1781/50000`.

The root symmetric old-degree gate and later asymmetric old-degree gates have strict fixed gaps below exponent one. Exact sufficient inequalities are

`9^1577<2^5000`, `13^13511<2^50000`, `7^1781<2^5000`.

Indeed they say respectively `2f0 log2 9<.1`, `A1 log2 13<.1`, and `Ainf log2 7<.1`. The finite integer comparisons are checked exactly. All other fresh-side and rounding powers are bounded by

`Ainf (2log2 13+1) < (1781/50000)(2·3701/1000+1) < .3`.

The elementary rational log upper bound is certified by `13^1000<2^3701` (also available in the prior proof); hence these have ample room below one. Newly created packet degrees have power at most Ainf<.9.

Use padding tolerance `lambda^-3`. Fixed positive power gaps absorb every O((log lambda)^2) buffer, the factor `s/M<lambda^(3/4)` at active calls and the required polylogarithmic packing losses. The same noncircular depth proof as the incoming tree schedule applies: provisionally consider depths up to `(3/4)log_3 lambda+O(1)`. There the tail tapers are at least

`lambda^{eta+o(1)}`, `eta=1−3ln(9/4)/(4ln3)>0`.

Packing is uniformly valid on this provisional range; tail child ratio is `2/7+o(1)<1/3`, so an active path cannot exceed the provisional depth. Floors are uniformly negligible and accumulated relative padding errors tend to zero. Thus

`M0≤s`, `M1≤(1+o(1))2s/9`,

`M_d≤(1+o(1))(4s/117)(2/7)^(d−2)`.

For retained i<u_d, `D=2^(a_d−i)≥2^(a_(d−1)+B+1)`. Inherited precision is `O(s lambda² 2^a_(d−1))`, whose ratio to `M D/u_d` is `O(lambda^(15/4)2^-B)=o(1)`. Hence the existing precision-six and weighted entropy interfaces remain uniform.

Leaves cost `2^{O(s/lambda^(3/4))}`; original entries cost `poly(s+L)2^{O(s^.9)}`; new packet entries cost `exp(s^(Ainf+o(1)))`. Each is lower order on `s/sqrt(lambda)`. All degrees, truncation lengths, coefficient coordinates and arithmetic bit lengths are polynomially bounded under the unchanged interface. Fixed polynomial overhead per level contributes only `O(lambda log lambda)` exponent bits.

## 6. Exact complete resource sum

Write `kappa=πsqrt(2)/ln2` and

`K0*=kappa/sqrt(f0)`,

`K1*=2kappa/(9sqrt(f1))`,

`K2*=4kappa/(117sqrt(f2))`.

In the tail the K ratio is `(2/7)/sqrt(4/9)=3/7`. The paid tail series is governed by

`alpha7/(1−3/7)=sqrt(3)/2 > b7`.

The complete time coefficient is the maximum of

`C0=b9 K0*`,

`C1=(4/9)K0*+b13 K1*`,

`Cinf=(4/9)K0*+(sqrt(24)/13)K1*+(sqrt(3)/2)K2*`.

Rigorous rational intervals, using alternating Machin arctangent bounds, a positive atanh(1/3) series for ln2, and integer-square-root brackets, give

`29.966734873162 < C0 <29.966734873163`,

`30.614393627106 < C1 <30.614393627107`,

`30.491276185937 < Cinf <30.491276185938`.

Therefore C1 governs time, while C0 governs space. Every deeper local table exponent is smaller than C0. With unretuned inherited fractions `(63/4000,9/800,77/16200)`, the same script certifies the matched pair30.629497100307…/29.985755335168….

## Evidence and boundary

- `matrix_checks/verify_rectangular_tree.py`: standard-library exact support/schedule verifier, authored in this iteration.
- `matrix_checks/verified_rectangular_tree.json`: normal output.
- `matrix_checks/verified_rectangular_tree_optimized.json`: equal output under `python -O`.
- `matrix_checks/check_rect_portfolio.py`, `rect_portfolio.json`: independent initial NumPy exploration of the same finite supports (not required for standard-library replay).
- `matrix_review.md`: static review of assigned source packets and comparison scope.

No incoming code was executed. No full fast matrix backend or full SAT solver is implemented here, and there is no measured SAT speedup. The new integer certificate supports the stated finite lemma; the uniform theorem also relies on the mathematical proof and unchanged imported exact interfaces. No Lean/Rocq formalization or independent validation of the upstream ETH conclusion is claimed.
