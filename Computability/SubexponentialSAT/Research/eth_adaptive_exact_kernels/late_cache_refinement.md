# Refined cached CRT/tree schedule: 35.07061367 time, 33.99950164 space

## Scope and attribution

This is an explicit schedule refinement of the newly received `subsat_contraction_tree` algorithm, not a new binary contraction-tree or fast matrix multiplication result. It uses that packet's weighted pair entropy, binary construction of group-block tables, exact integer-coordinate/CRT bridge to a fixed field multiplication algorithm of exponent12/5, and pays all recursive child oracles. It retains the same normalized <=s Boolean wires, maximum degree<=ceil(s^.9), original entry-cost and immutable creation-precision interface, and all unchanged source identities.

The refined bounds are

`T <= poly(s+description) * 2^((C_T+o(1))*s/sqrt(log2 s))`,
`S <= poly(s+description) * 2^((C_S+o(1))*s/sqrt(log2 s))`,

where

`C_T = pi/ln(2)*sqrt(7125/119) =35.07061367045685...`,
`C_S = pi/ln(2)*sqrt(46875/833)=33.99950164415886...`.

Thus eventual coefficients35.071 for time and34 for space are rigorously valid. Both coefficients improve the late contraction-tree packet's35.3545880584 time and34.2748030050 space. This is a subexponential-space result; it is separate from the polynomial-space separator improvement and from lower-degree specializations.

## Exact schedule and feasibility

Let lambda=ceil(log2 s), b=ceil(6log2 lambda), and H=ceil(s/lambda^(3/4)). Set

- root alphabet r0=8 and retained fraction x=833/50000;
- every later alphabet rd=12;
- first tail fraction y=5003/540000 and subsequent fractions y/6^(d−1);
- ud=floor(lambda times its fraction), ad=sum_(j<=d)(uj+b).

The identity `x+y/(1−1/6)=1/36` gives total leading packet budget1/36.

Root symmetric packing exponent is `.9+6x=24999/25000<1`.
Below root, retained-side exponent is at most `.9+log2(12)/36<1`.
The integer inequality12^100<2^359 gives a strict rational upper3599/3600 for the latter. Fresh-side and rounding exponents are bounded by `(1+2log2 12)/36<1`, and generated tensor degrees have exponent1/36+o(1)<.9. These fixed margins absorb all polylogarithmic factors and additive buffers.

Use precisely the late packet's noncircular depth argument: for hypothetical active depths up to `(3/4)log_5(lambda)+O(1)`, the retained ranges are at least lambda^(eta+o(1)), where eta=1−3ln6/(4ln5)>0 because6³<5⁴. Lossless packing is therefore valid uniformly. Root shrink is1/4+o(1), tail shrink1/6+o(1), eventually<=1/5; an active path cannot exceed the hypothetical bound. Floors have uniform relative o(1) error, and the accumulated padding error over O(log lambda) depths is1+o(1).

Inherited precision obeys O(s lambda²2^a_previous). Since active s/M<=lambda^(3/4), additive gap b makes its ratio to MD/u at mostO(lambda^(15/4)2^-b)=o(1). The exact Hermite taper therefore retains child precision at most(6+o(1))MD/u, and the mode entropy estimates are unchanged. Leaves cost2^{O(s/lambda^(3/4))}, original entries2^{O(s^.9)}, packet entriesexp(s^(1/36+o(1))); all are lower order. Polynomial indexing and access costs over logarithmic depth contribute onlyO(lambda loglambda) to the logarithmic runtime.

## Fully charged recurrence

Write `k=pi sqrt2/ln2`, `K0=k/sqrt(x)`, `K1=k/(4sqrt(y))`, and `gamma=1/sqrt6`. These are coefficients on s/sqrt(lambda); tail depthd has coefficientK1 gamma^(d−1).

The inherited exact pair-cardinality ledger gives

- root r8, blocks3,3,2: cache `a8=sqrt14/8`, binary-tree/triangle work `b8=sqrt(798/25)/8`, memory `j8=sqrt30/8`;
- tail r12, blocks4,4,4: cache `a12=sqrt22/12`, work `b12=sqrt(1728/25)/12=2sqrt3/5`, memory `j12=2/3`.

Binary merge cardinalities are `2a(r−a−b),2ab,2b(r−a−b)`; the fixed-field exponent12/5 gives cost square `sum(v)−(21/25)min(v)`. The largest root/tail merges are smaller than their final triangles, exactly as in the late source. All singleton function evaluations remain actual recursive child contractions.

Suppressing polynomial factors, `T_d <=2^(a_rd K_d) T_(d+1)+2^(b_rd K_d)`. Unrolling the entire tail yields

`C_T = max{b8K0, a8K0+K1 max(b12,a12/(1−gamma))}`.

The exact checker proves `a12/(1−gamma)<b12`. It also proves

- root candidate b8K0=35.07061367045685...;
- full descendant candidate a8K0+b12K1=34.76012692734665... <root.

This is not merely a root-local calculation. The tail coefficient includes every ancestor cached-child enumeration, and the limiting tail contribution is bounded as well.

Storage is the maximum (not sum of exponents) of resident ancestor/descendant tables, with polynomially many frames and polynomial CRT/coordinate bits per cell:

`C_S=max(j8K0,j12K1)`.

Root space33.99950164415886 exceeds tail11.09864058511854, proving the displayed space value. Sequential fixed-base matrix multiplication has quadratic element storage; sorting/reshaping and CRT storage have polynomial overhead per table entry, as in the imported bridge. No unit-cost enormous-integer or free-group-oracle assumption is introduced.

## Exact evidence

`late_cache_checks/verify_late_cache.py` is newly authored and imports no archive code. It uses explicit exception-based gates, so all checks remain active with `python -O`. Normal and optimized runs passed. `late_cache_checks/late_cache_checks.json` records exact rational enclosures and symbolic constants.

The checker validates every packing margin, budget identity, tail growth, complete-recursion dominance, memory maximum, and strict comparison with the late source. Pi and ln2 are enclosed by rational Machin/atanh series; square roots are enclosed by integer square roots. No floating-point number decides a proof gate. Decimal displays are only explanatory.

The existing field theorem is a theoretical backend, not implemented here. The primary arXiv paper2404.16349 supports a strict exponent below12/5. Its CRT bridge, rather than arbitrary division inside the2-adic coefficient ring, is essential. No end-to-end SAT timing, independent proof-assistant certification, global schedule optimum, or numerical coefficient per SAT variable is claimed.

## Broader portfolio caution

Composing only the new backend with our previous root7/multi-depth cached schedule gives37.324611..., because paid descendant caches dominate. Reporting its smaller local root value34.508009 would be incorrect. The root8/tail12 retuning above is the actually established stronger composition. Lower-memory or lower-degree branches from the incoming packets remain useful and should be preserved separately.

## Optional lower-memory companion (also exactly certified)

Retain the entire root7/multi-depth schedule from `cache_schedule_new.md`, but replace each call's flat/Strassen evaluator by the late CRT/tree evaluator. Define squared local factors `(a_r²,b_r²,j_r²)` as follows:

|r|cache²|binary-tree work²|memory²|
|--|--|--|--|
|7|12/49|632/1225|24/49|
|9|16/81|12/25|4/9|
|8|7/32|399/800|15/32|
|6|5/18|12/25|4/9|
|5|8/25|316/625|12/25|
|4|3/8|13/25|1/2|
|3|4/9|12/25|4/9|

These follow from the same exact merge/triangle cardinalities, not a free-table assumption. Write `x_d,m_d` for that schedule's retained fractions and wire ratios, `K_d=(pi sqrt2/ln2)m_d/sqrt(x_d)`, and `P=sum_(d=0)^6 a_(r_d)K_d`. Its tail begins with r3, m7=1/1890, x7=239/40000 and geometric work ratio gamma=4/(3sqrt3). The complete tail candidate is

`P + K7 * a3/(1−gamma)`.

The exact checker proves this exceeds every finite-prefix candidate `sum_(h<d)a_(r_h)K_h+b_(r_d)K_d`, and the local tail alternative `P+b3K7`. Thus its time coefficient is37.32461123868779... . Root boundary storage remains dominant, with coefficient33.62304092165775... . Eventual bounds37.325 time and33.624 space are certified. This is slower than the new main35.0706 variant but uses a smaller space exponent.

`late_cache_checks/verify_lowmemory_companion.py` and `lowmemory_companion_checks.json` contain the explicit integer/rational proof gates and factor ledger. Normal and `python -O` runs both passed. All source packing, buffer, cutoff and entry-cost proofs are unchanged because this companion changes only the evaluator. This optional row is a genuine time/space tradeoff, not evidence against the stronger main time theorem.
