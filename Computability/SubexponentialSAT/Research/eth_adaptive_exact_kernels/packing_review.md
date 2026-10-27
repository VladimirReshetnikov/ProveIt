# Review of the three new packing proposals

Repository snapshot: `VladimirReshetnikov/ProveIt@ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`.
Inspected locally extracted report TeX, supporting annulus TeX and packing implementation sources. No archive-provided program was executed. This is a static mathematical/component review, not full independent certification of the inherited tensor contraction or ETH theorem.

## Immediate comparison result

The previous coefficient 94.7482022595 is **not** the best newly supplied generic normalized certificate. The asymmetric archive proves 76.9089949516, and its appendix already derives a same-alphabet boundary infimum 76.4327736858. The joint-Cauchy review (separate reviewer) supplies slope four at unchanged mode-family multiplicity and child topology, so the correct combined slope-four comparisons are these numbers multiplied by `sqrt(3)/2`. The stronger boundary composition is approximately 66.1927236936. A practical implementation should also retain low-degree specializations and exact annulus/factorial weights where useful; generic wire coefficients must not be transplanted directly to SAT-variable coefficients.

All three reports preserve the general density envelope
`poly_k(n,m) * 2^{O_k(n min(log(2+m/n),log log n)/sqrt(log n))}`.
They do not establish a new logarithmic order, an end-to-end SAT solver, or machine-checked formalization.

## Asymmetric packet balancing

Archive: `eth_asymmetric_packet_balancing_2026-10-26.zip`.
Main coefficient: `pi*sqrt(5/2)*(9+sqrt(3))/ln(2) = 76.9089949516...` for <=s wires, maximum degree <=ceil(s^.9), initial precision/truncation O(s), and inherited creation-precision/entry-oracle interface.

### Constructive packing lemma

For maximum row degree R, column degree C, Q labels, integer h>=2, greedily balance whole row vertices by degree. Then choose whole column labels by exact-rational conditional expectation with `q=1+1/(hC)` and potential `sum_ab q^{X_ab}`. It proves

`max X_ab <= (1+2/(h-1))*(M/Q^2+R/Q) + 2(hC+1) ln Q`.

Static proof checks:
- Greedy row loads are <=M/Q+R, including multiedges.
- Conditional expectation factors over whole column vertices; no independence of parallel edges is assumed.
- Convexity gives `q^w-1 <= (w/C)(q^C-1)`.
- `1/ln q<=hC+1` and `(q^C-1)/(C ln q)<=1+2/(h-1)` follow as stated.
- Every conditional expectation is a rational of polynomial bit length.

With h~log s, common-pair padding is asymptotically lossless provided
`QR/M=o(1)`, `Q^2 C (log s)^2/M=o(1)`, and `LQ^2/M=o(1)`.
This differs materially from symmetric D_arr*Delta packing: below root the retained side has R<=Delta, while the fresh side has C<=2L_previous. The algebraic child construction really does place all retained parent tensors from both sides on one new side and all new packet tensors on the other.

Packet family counts retain the exact unequal-symbol saving:
`c_i <= (2(1-1/r)+o(1))*M/D_i`; child size `(2/r+o(1))*M`.

### Precision/schedule

Uses inherited exact Hermite taper `rho=(1+o(1))*M/u` and sufficient child precision `p+6rho D_i+rho u(a+1)`. New gap is `b=ceil(6 log2 lambda)`, `a_d=a_(d-1)+u_d+b`. Active cutoff M>s/lambda. Consequently inherited p and secondary Hermite loss are lower order, uniformly, and `p_i<=(6+o(1))*MD_i/u_d`.

Main fixed schedule: r=16; root u0=floor(lambda/81); tail ud=floor(lambda/(108*4^(d-1))); cumulative retained budget2lambda/81. Root packing exponent809/810; below root QR has same exponent, while fresh-column and rounding powers are <=2/9. Coarse child shrink1/6 closes depth bootstrap and sharp shrink1/8 gives path factor9+sqrt3.

Appendix explicitly recognizes root budget `(1-gamma)/(2log2 r)`, tail total cumulative capacity twice this, and derives optimized geometric allocation. At gamma=.9, r16 it identifies excluded-boundary coefficient76.4327736858. Thus merely moving fixed denominator81 toward80 is not an intellectually new optimization; an implementable vanishing-slack attainment would close an already identified boundary.

Low-degree specialization (root degree<=s^(1/12)) certifies31.0641320630, with r48, u_d=lambda/(14*8^d), cumulative4lambda/49. Generic symmetric intermediate coefficient93.9291064374 uses denominator128. These are separate degree premises, not generic dominance statements.

### Annulus modes

Supporting `annulus_modes.tex` constructs an explicit 2-ordering of `S_i={w in Z_(2):0<=v2(w)<=i}`. Let F_i(b) be generalized factorial valuations obtained by sorted merge of `G(n)=n+v2(n!)` and `n+F_(i-1)(n)`. It proves `F_i(b)>=v2(b!)` and uniform `F_i(b)=(1+3/(4^(i+1)-1))*b+O(log(b+2))`. Actual reciprocal-row congruences transfer the divisibility to the unramified extension ring; arbitrary extension-ring binomial integrality is not assumed. Resulting exact weights
`omega_i(b)=R+b+F_i(b)+v2(b!)`
are termwise >=factorial weights at the same baseR; slopes4,16/5,64/21,... tend3. Cauchy telescoping identity, unit denominators, point-size bound and perturbation argument appear internally coherent on static inspection. This cannot by itself improve uniform slope3, as report correctly states. Joint full-block slope4 is a different stronger decomposition, not justification to multiply both gains.

### Existing implementation and new practical opportunity

`code/balanced_packing.py` already caches powers q^0..q^M, whole future row products, and removes each current factor once. It nevertheless evaluates each candidate column label with an inner scan over every row label and every pair-load column: O(Ncol Q^3) rational arithmetic, after setup. It does **not** use candidate-delta sparsity.

Parent's independently derived improvement is valid. At column j let `F'_a` be future product after removing j, `U_a=F'_a(q^{w_aj}-1)`, and `delta_b=sum_a U_a(q^{load_ab}-1)`. Then exact candidate conditional expectation is
`current + delta_b - (sum_c delta_c)/Q`.
Only rows with nonzero w_aj and cells with positive assigned load contribute. Every term is nonnegative. Missing labels have score zero; first missing label is lexicographically first optimum whenever any is absent. Thus sparse score dictionaries give precisely the original choices, using at most O(MQ) score arithmetic after aggregation, not merely beating a deliberately naive baseline. The same identity reconstructs full candidate certificate values.

## Balanced packing

Archive: `eth_balanced_packing_2026-10-26.zip`.
Main coefficient `9pi/(4ln2)*sqrt(15log2 54)=94.7482022595...`, identical to our previous bundle's main coefficient. Two-stage polynomial exact-rational balancing, nearly lossless common padding, additive guard, and integer-cap schedule attain this asymptotic coefficient. It compares fairly with old factorial-adjusted optimized-family boundary~368.654 rather than only374.378.

Sufficient gate `M>=4 Q^2 Delta lambda^4`, q=`1+1/(Delta lambda^2)`, strict maximum cell bound `<ceil((1+2/lambda)M/Q^2)`. Static polynomial inequality and expectation proof are sound as written. Its code `derandomize_columns` invokes full conditional-potential recomputation for every candidate at every column, so it is strictly less optimized than the asym archive's cached implementation. No sparse-delta scoring was present.

## High moment

Archive: `eth_high_moment_2026-10-26.zip`.
Main coefficient again94.7482022595, using a mathematically different deterministic higher-even-moment construction. Greedy proper edge coloring K<=2Delta-1 partitions edges into independent matchings; Holder/MGF yields
`max |X_gamma-mu| <=4D^(1/(2t))*max(sqrt(t K mu),tK)`.
Conditional moments are expanded in ordered edge tuples up to degree2t, with common rational denominator. t=ceil(log2 s) incurs **quasipolynomial** setup `2^{O((log s)^2)}`, explicitly paid as lower order. Fixed t gives polynomial setup but coefficient factor sqrt((t+1)/t). The report does not misrepresent growing-t derandomization as polynomial.

Orbit-adaptive padding is a distinct polynomial-time alternative:
`W <= M + sqrt(2 M Delta [r(2r-1)]^a) + [r(r+1)]^a`.
This follows from orbit maxima, Cauchy-Schwarz, exact sum of squared orbit sizes and orbit count. It has weaker coefficient98.8967002322 for r64. Orbit padding remains a potentially useful finite instance-sensitive candidate but is not the best asymptotic generic frontier.

Precision gap nu^2 at each depth is paid by cubic reserve2nu^3; integer root capacity `max{j:54^(20j)<=2^lambda}`. Degree-sensitive formula limits packet capacity by both original degree and newly created packet degrees, so it avoids incorrectly treating bounded-degree input as bounded degree throughout recursion.

## New schedule opportunity identified during review

One can vary alphabet by depth because each recursive call creates a fresh labeling and packet decomposition. Below root only the retained-side constraint `a_d log2 r_d + .9 lambda < lambda` is binding at leading order; fresh-side and rounding constraints remain far below one. A numerical backward DP over this *new* scheduling family suggested joint-Cauchy coefficient~63.7552, rather than66.1927 for constant r16.

A clean strictly feasible rational schedule, independently computed with elementary arithmetic, achieves coefficient63.7589940749:
- depths0..6 alphabet `[13,14,8,6,5,4,4]`;
- cumulative retained fractions `[27/2000,21/800,333/10000,1933/50000,861/20000,1183/25000,4999/100000]`;
- tail r3 with retained budget B=1301/100000 and ratio3/4, reaching cumulative limit63/1000;
- exact local slope-four cost `kappa(r)=pi*sqrt(2(1-1/r))/ln2`;
- tail leading mass1/5460 and geometric path factor `1/(1-(2/3)/sqrt(3/4))`.

The optimizer agent has received the precise rational data and owns the rigorous all-size construction/certificate; this review is not a claim that the numerical DP proves global optimality. Constant strict gaps absorb logarithmic buffers. For the tail choose a coarse child ratio7/10, lying strictly between2/3 and3/4; the noncircular cutoff-depth argument then ensures the smallest active retained count grows as a positive power of lambda. We retain the same generic premise, polynomial space and inherited algebraic dependencies.

## Seven-arrival comparison matrix (cross-review synthesis)

All rows below are generic normalized wire certificates unless explicitly restricted. `Joint-compatible` means substituting the full-block slope-four Cauchy decomposition while retaining that row's supplied packing/schedule and polynomial-space recursion. It does not assert global optimality over every schedule one could invent by combining primitives.

| New arrival | Supplied generic coefficient | Joint-compatible coefficient / status | Distinguishing contribution |
|---|---:|---:|---|
| `eth_asymmetric_packet_balancing` |76.9089949516|66.6051434076|Side-sensitive packing, additive gap, crossing fraction; fixed r16|
| Same archive, boundary family |76.4327736858|66.1927236936|Explicitly identified excluded-boundary infimum, not a fixed equality theorem|
| `eth_balanced_packing` |94.7482022595|82.0543501197|Polynomial two-stage balancing, integer capacity reaches boundary|
| `eth_high_moment` |94.7482022595|82.0543501197|Quasipolynomial growing-moment setup; fixed-moment polynomial variant|
| `eth_packet_refinement` |95.6639404729|82.8474026757|Matching-based derandomization, additive gap; own boundary94.7482022595|
| `eth_recursive_refinement` |133.2073724925|116.2729271567|Variance packing; existing mode slope64/21, so replacement factor is sqrt((64/21)/4), NOT sqrt3/2|
| `3sat_round2_refinement_20261027` |84.0662714942|72.8035267154|Matching potential, root37/tail8 schedule, exact crossing fraction|
| `eth_joint_cauchy` |319.6857570777|Already slope4|Full-block joint basis; deliberately retained older packing/schedule|
| Our previous `eth_matching_refinement` |94.7482022595|82.0543501197|Dominated by supplied asymmetric certificate; cannot be reused as main new result|

The exact replacement factors, rather than rounded decimal displays, are the comparison evidence.

**Different memory frontier.** Joint-Cauchy also supplies subexponential-space cached/Strassen contraction. The separate Cauchy reviewer derives the valid composition with the asymmetric fixed r16 schedule as time coefficient44.53757185496 and space coefficient39.49594953370 (split5,5,6). Hence the new polynomial-space coefficient63.758994 is not a uniformly smaller unrestricted-time bound. It improves a specified polynomial-space resource frontier. The practical sparse packing update is compatible with either memory regime, and the complete portfolio should retain the prior high-memory option.

**Different degree frontier.** Asymmetric low-degree31.064132063 becomes26.9023275131 under joint modes; its root premise degree<=s^(1/12) is stronger. A generic <64 theorem does not replace that specialized option. Source SAT reductions have their own wire constants and degree information.

### Source anchors for practical comparison

- Asymmetric `code/balanced_packing.py`: function `balance_pair_labels` starts line20; powers table lines43–46; future row products lines64–69; per-column future removal line77; candidate nested row/cell sum lines79–85; final update lines95–100. This is the strongest directly comparable cached implementation reviewed.
- Balanced `code/packing.py`: `conditional_potential` starts line90; full row/unassigned-product reconstruction lines110–122; `derandomize_columns` starts line159; full recomputation per choice line172.
- High-moment report Section3 / Lemma3.1: explicit centered-power expansion into ordered edge tuples, polynomial space and `(M+1)^{O(t)}` setup; different algorithm, not the candidate-delta kernel.
- Asymmetric report theorem labels `thm:pair-balance`, `lem:side-degree`, `eq:family-count`, `eq:main-schedule`, `app:optimization` provide the mathematical interface and strongest supplied generic family.

### Additional degree-aware reduction result that must be retained

High-moment Section `sec:applications` does more than give an abstract degree parameter: it explicitly replaces the source query-group count by
`J=ceil(sqrt(n)/ceil(log2 n)^2)`. It states that this preserves O(n log log n) wires while reducing initial maximum degree to `n^(1/2) polylog(n)`, with degree-array enumeration `2^{O(n/(log n)^3)}` and unchanged coefficient-entry procedure. Its normalized coefficient becomes94.7482022595/sqrt5≈42.3727, or approximately36.695 after joint slope-four modes. The source regrouping proof is another imported reduction dependency, not certified here end-to-end. Recursive-refinement's analogous n^.495 group choice gives gamma=.51 and coefficient60.7069575490 under slope64/21. Therefore comparing the new generic gamma=.9 coefficient63.759 directly to these SAT-specific inputs would be invalid; retain the specialized ledger.

A new easy schedule extension was sent to the optimizer: multiply all seven finite-prefix retained/cumulative fractions by4; keep their alphabets; set the tail cumulative limit to239/1000, leaving tail budget244/6250 and ratio3/4. This is feasible for initial degree<=s^.6, hence covers n^.5 polylog after normalization. Row/root guards follow by multiplying the earlier log guards by4. Fresh-side bounds are dominated by rounding because previous cumulative budget<=current. The finite-prefix rounding exponents are approximately .45365,.90454,.9324,.95412,.97187,.9464,.9998, and tail rounding exponent is `.239*(1+2log2 3)=.996612...<1`. Its coefficient is31.8851390530<32. The optimizer owns all-size proof and exact certificate of this extension. This strengthens the normalized lower-degree ledger without asserting a variable-level numerical SAT coefficient or replacing the still-better bounded-degree specialization26.9023.

### Independent audits completed

- `asym_schedule_new.md`: exact budget guards, fresh-side/rounding exponents, hypothetical-depth bootstrap, uniform floors, additive precision guard, local entropy, path sum and polynomial resource charges checked and internally consistent.
- `sparse_delta_proof.md` / `code/sparse_balancing.py`: exact score identity, positive support, lexicographic absent-label minimum, Q=1, zero columns, exponent index bounds, common-preprocessing comparison and dense-output charges checked and internally consistent.
- Existing two-stage alphabet idea can be combined more strongly than fixed-r16: root17/tail13 with capacities A0=.1/(2log2 17) and A=.1/log2 13 gives boundary66.1204754600. This is an explicit combined candidate, not a proved globally optimal family minimum. New63.758994 still improves it.

## Final degree-0.51 specialization audit

Independently audited `asym_schedule_checks/verify_degree_51_schedule.py` and its recorded `degree_51_schedule_checks.json`. The final specialization supersedes the earlier suggested <32 schedule: alphabets `[15,15,8,6,5,4,4]`, cumulative budgets `[.0627,.11345,.1428,.162,.1771,.1911,.1999]`, tail alphabet3, total limit.239 and geometric ratio3/4.

**Result: PASS.** Independently recomputed every strict logarithmic guard through integer powers, all positive increments, tail mass1/6750, remaining tail budget391/10000, and coefficient29.353412008627856. The supplied one-sided rational certificate `309386069468981/10537797414375 =29.359652430491405... <30` follows the same valid Machin/atanh and rational-square-root construction as the main checker.

The necessary packing checks are complete, not merely row-degree checks:
- Root: `.51+2 A0 log2(15)<1` controls Q²C; QR is smaller.
- Nonroot retained side: `.51+A_d log2(r_d)<1`.
- Every level: `A_d(1+2log2 r_d)<1` controls padding-rounding LQ².
- Fresh side: `2A_d log2(r_d)+A_(d-1) <= A_d(1+2log2 r_d)<1`, because the cumulative budgets are increasing. This also holds uniformly in the infinite tail using its limit.239.
- Newly created tensor degrees have exponent at most.239+o(1)<.51, preserving the retained-side degree invariant.

The strict margins absorb additive O((log lambda)²) buffers and polylogarithmic terms. The same noncircular `.7` child-shrink bootstrap and ratio.75 tail give diverging active taper lengths. Precision inheritance and slope-four entropy transfer unchanged; packet-entry exponent.239 remains below the allowed original-entry exponent.9 and below the leading contraction scale. Polynomial-space depth-first traversal is preserved.

The incoming high-moment SAT regrouping gives n^.5 polylog(n) initial degree; with the customary root normalization s>=n and s=O_k(n log log n), this is eventually <=s^.51. Thus the <30 theorem covers that imported grouping, without assigning the wire coefficient30 directly to SAT variable count n. This is a polynomial-space specialization; it is not claimed to dominate the cached/Strassen higher-memory time frontier or the narrower bounded-degree specialization (which remains available). The existing upstream algebraic identities and regrouping correctness remain explicit dependencies.
