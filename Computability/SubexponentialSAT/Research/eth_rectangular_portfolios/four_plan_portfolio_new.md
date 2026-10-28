# Four-plan rectangular portfolios: final strengthened certificate

## Headline

Keeping the already certified **retuned `9→13→7` schedule unchanged**, replace the three-plan local menus by the explicit four-plan menus below. The resulting generic normalized bound is

- **Time:** `30.491276185937…`; safe eventual coefficient **30.492**.
- **Space:** `28.853020941407…`; safe eventual coefficient **28.854**.

The coefficients multiply `s/sqrt(ceil(log2 s))` in a base-two exponent. This is subexponential space. The strongest comparable incoming pair is `30.891018920366… /30.753912832055…`; both improve. The common degree/entry/precision/oracle assumptions and imported exact identities are unchanged. The SAT logarithmic order is unchanged; no full fast backend or SAT solver is implemented.

This four-plan construction is an additional concrete contribution, beyond the first rectangular/three-plan composition. The three-plan theorem and its evidence remain valid as a matched ablation. This experiment was bounded in advance: one affine-plane menu for r=9 and exactly three explicit possible fourth plans for r=13. There is no claim of globally optimized plans or schedules.

## Four plans at r=9

Identify vertex `3x+y` with `(x,y)∈F_3²`. Use the four parallel classes: vertical lines, and slopes0,1,2. Within each listed block the order is part of the plan, since binary table construction recursively splits after `floor(k/2)` elements.

1. `(0,1,2) | (3,4,5) | (6,7,8)`
2. `(0,3,6) | (1,4,7) | (2,5,8)`
3. `(0,4,8) | (1,5,6) | (2,3,7)`
4. `(0,5,7) | (1,3,8) | (2,4,6)`

Every pair of vertices belongs to a common block in exactly one parallel class. This supplies a natural explicit menu; validity of the coefficient below is established by its complete operation-support certificate, not by assuming that pair coverage alone bounds all operations.

## Four plans at r=13

Keep all three plans of the incoming tree-certificate packet and append the fourth plan produced by the permutation `x↦5x+3 mod13`, split into block lengths5,4,4:

1. `(0,1,2,3,4) | (5,6,7,8) | (9,10,11,12)`
2. `(12,10,1,6,4) | (9,0,3,8) | (5,2,7,11)`
3. `(0,8,11,12,1) | (7,10,4,3) | (5,2,6,9)`
4. `(3,8,0,5,10) | (2,7,12,4) | (9,1,6,11)`

The other two tested fourth permutations, `2x+1` and `3x+2 mod13`, gave squared local coefficients `112953937728479/331240000000000` and `113129558528479/331240000000000` respectively. Both improve the three-plan coefficient, but the displayed `5x+3` candidate is smaller. No further search was performed.

## Exact four-plan local lemma

Use the same rectangular bridge and scale `L0=1,400,000` proved in `rectangular_tree_new.md`: all operation forms are permutations of `(1400007,1400007,0)` and `(1400000,1175014,750000)` on the three edge classes, zero within parts. For each of the four plans let `V_j` be its complete deduplicated support set. Define

`Q_r=max_(v_j∈V_j,j=1,…,4) ||v1+v2+v3+v4||₂²`.

The finite averaging proof is unchanged except that four replaces three:

`min_j F_j(g)≤(1/4)Σ_j F_j(g)`

`=(1/(4L0)) max_(v1,…,v4) (v1+…+v4)·g`.

Repeating each undirected coefficient on both directed orientations and applying the inherited weighted entropy bound gives

`b_r²=2 Q_r/(16r²L0²)`.

Because the output branch remains part of every operation cost, the selected-plan local storage is bounded by the same coefficient. The finite menu can be selected with exact integer products or ceiling logs, just as before. No new arithmetic, counting, or child-entry oracle is introduced.

The exact certificates are:

|r|supports per plan|support quadruples|Q_r|b_r²|
|---:|---:|---:|---:|---|
|9|57|10,556,001|405,850,918,811,760|563681831683/1764000000000|
|13|89|62,742,241|895,372,728,026,656|27980397750833/82810000000000|

Thus `b9=.565285347085716…` and `b13=.581280226306888…`.

## Complete paid time and space

Retain the previously certified fractions exactly:

`f0=1577/100000`, `f1=2813/250000`, `f2=1433/300000`, tail fractions `f_(2+j)=f2(4/9)^j`.

All strict packing, noncircular depth, precision, leaf and entry-cost gates from `rectangular_tree_new.md` are unchanged. In particular, the root arity is9, depth-one arity13, tail arity7, and the root-to-tail wire multipliers are `1,2/9,4/117`. Let

`K0*=κ/sqrt(f0)`, `K1*=2κ/(9sqrt(f1))`, `K2*=4κ/(117sqrt(f2))`, `κ=πsqrt(2)/ln2`.

The singleton child-call factors remain `α9=4/9`, `α13=sqrt(24)/13`. Retain the old r7 square-backend tail, whose cache-series coefficient is `sqrt(3)/2`, larger than its local aggregation coefficient. The complete paid time maximum is therefore the same three expressions:

`C0=b9 K0*`,

`C1=(4/9)K0*+b13 K1*`,

`Cinf=(4/9)K0*+(sqrt(24)/13)K1*+(sqrt(3)/2)K2*`.

Exact rational intervals are

- `28.853020941407 < C0 <28.853020941408`;
- `30.490561591676 < C1 <30.490561591677`;
- `30.491276185937 < Cinf <30.491276185938`.

Now **the infinite paid-cache tail bound governs time**, narrowly above C1. This is a maximum of the coefficients of unrolled finite recursion paths, with the infinite geometric series only an upper bound; it does not mean the algorithm recurses infinitely. The same uniform o(1) arguments and finite leaf threshold apply. Root local tables govern space, so C0 is the space coefficient.

No additional fraction transfer is needed. In particular, the suggested tiny transfer from f1 into f2, preserving total leading capacity, locally increases both C1 and Cinf at these parameters and would not improve the maximum. The schedule is intentionally frozen rather than carrying out another optimization search.

## Reproducible exact evidence

`matrix_checks/verify_four_plan.py` is a new **standard-library-only** verifier. It imports only our own `verify_rectangular_tree.py` to reuse the independently authored support construction and rational interval routines. It reads or executes no incoming archive code.

All **73,298,242 quadruples** are exhausted using exact Python integers. To avoid a repeated coordinate loop, the verifier precomputes pairwise Gram products and expands

`||Σv_i||²=Σ||v_i||²+2Σ_(i<j) v_i·v_j`.

For fixed first/second supports, each third/fourth-support pair is examined once. This is exact arithmetic, not a numerical norm or relaxation. A maximizing tuple is independently reconstructed coordinate by coordinate. Runtime is about seven seconds per normal or optimized execution in the present environment. No NumPy installation or compiler is needed to replay the final certificate.

Files:

- `matrix_checks/verify_four_plan.py`
- `matrix_checks/verify_rectangular_tree.py` (its own-code dependency)
- `matrix_checks/verified_four_plan.json`
- `matrix_checks/verified_four_plan_optimized.json`

Normal and `python -O` outputs are byte-identical; checks use explicit exceptions, not disabled assertions. The separate bounded NumPy experiment also gave the same exact maxima; it is optional exploratory evidence and not required for replay.

All original proof boundaries remain: finite certificate checks do not independently validate the full upstream ETH manuscript, and no Lean/Rocq proof or measured SAT speedup is claimed.
