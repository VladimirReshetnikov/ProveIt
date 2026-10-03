# U9 tail-shift grouping: 257/604 and a 43-witness endpoint261/312

The [fresh finite optimizer](neary_woods_universal_tail_partitions.py) and
[receipt](neary_woods_universal_tail_partitions.json) improve the complete U9
compiler's **degree upper bound at261 operations from372 to312**, retaining
43 positive witnesses. At257 operations the bound falls from710 to604;
at258 it falls from664 to558. The actual final polynomials, including every
ordinary constraint and finalizer, attain these upper-bound ledgers. The
minimum operation count in this family remains253, and the separate universal
records remain **74 certificate /86 polynomial operations**.

This is a new optimization over exactly **eight eligible native bases**, each
with two duration interfaces. The [all-sixteen transfer](neary_woods_tail_quotient_all16.md)
provides their canonical complete sources and positive-zero theorem. The eight
additional native bases with unprojected joint scale are unchanged; their
frozen minima are read separately when forming the combined catalogue below.
No historical compiler or old census is executed.

Every degree below is an upper bound on the formal polynomial with ordinary
input, supplied program parameters and positive witnesses of degree1. The
11 fixed numeral recipes have degree0. Exact optimization of these guarded
bounds is not an exact polynomial-degree claim, nor a lower bound on arbitrary
arithmetic circuits. Specializing program parameters can lower the degree.

## Complete source witnesses

The new eligible 43-witness frontier is:

| Operations | M | A | Degree upper bound | Geometry / joint strong | Finalizer |
|---:|---:|---:|---:|---|---|
|253|132|121|982|normalized / normalized|one anchor|
|255|132|123|848|normalized / ordinary|one anchor|
|256|131|125|802|ordinary / ordinary|one anchor|
|257|132|125|604|normalized / ordinary|two SOS groups|
|258|131|127|558|ordinary / ordinary|two SOS groups|
|259|132|127|404|normalized / ordinary|three SOS groups|
|260|131|129|398|ordinary / ordinary|three SOS groups|
|261|132|129|312|normalized / ordinary|four SOS groups|

Both scale coordinates are projected in every row of this table. The
ordinary joint strong residual remains at degree bound122 wherever present;
its square is included. The two257 group bounds are302 and302, and the two258
group bounds are279 and279. At261 the four group bounds are156,150,150,148,
so the full SOS bound is312, including the retained strong residual.

The eight eligible bases also give the separate44-witness frontier

```
257/975,258/837,259/795,260/594,261/552,262/398,264/312.
```

These rows retain the unprojected geometry scale and its ordinary comparison.
The receipt stores **thirty complete source arrays**: the union of the eight
43-witness and seven44-witness winners, each at both duration interfaces.
It also compiles, recounts and records source hashes for **all240 per-group
minimizers**, totaling64,918 paid gates. It does not claim that all240 complete
arrays are saved. The CLI deterministically rebuilds all of them.

The ordinary input remains x. The merged interface has four fixed positive
program parameters; the other retains its separate fifth duration parameter.
All factors, witnesses, paid numeral products, loading and history gates are
retained. A fixed valid program slice represents computations of unbounded
length; no time limit or substituted small numeral table is introduced.

## Actual changed cores and degree weights

The code independently reads the literal16 source arrays from the frozen
[product-scale receipt](neary_woods_universal_product_scale253.json), applies
only the proved tail-operand replacement, and checks equality to all16 saved
successors. It derives each core by taking the dependency closure of every
individual unit-factor port and both operands of every ordinary comparison.
This discards only the old product spine and finalizer, then emits the chosen
new products and complete finalizer.

The source-derived eight-base ledgers are:

| Base | Strong normalizations | Geometry projected | Core M+A | Factors | Ordinary comparisons | Largest residual bound | Unrestricted-group floor |
|---:|---|---|---:|---:|---:|---:|---:|
|0|none|No|235=115M+120A|14|3|122|312|
|1|none|Yes|235=115M+120A|14|2|122|312|
|2|geometry|No|236=116M+120A|15|2|122|312|
|3|geometry|Yes|236=116M+120A|15|1|122|312|
|4|joint|No|236=116M+120A|15|2|14|688|
|5|joint|Yes|236=116M+120A|15|1|14|688|
|6|both|No|237=117M+120A|16|1|2|688|
|7|both|Yes|237=117M+120A|16|0|0|688|

Every joint scale is projected. Bases0–7 and8–15 are paired duration
interfaces with identical weights and core counts, rather than sixteen
different optimization problems. The complete factor vectors and ordinary
operand pairs are in the receipt.

Each degree calculation authenticates the two main-norm producer cones before
using the all-value expansion

```
(X+ac+G)^2-(a^2+H)c^2 = (X+G)(X+G+2ac)-Hc^2,
H=4a+3, G=ga*H.
```

Every other gate uses multiplication/addition upper-degree propagation. In
particular, the ordinary strong equation is never used as a formal polynomial
identity, and computed k is not replaced by a native value known only at zeros.
The older canonical bounds are reproduced before the new search begins.

## Paid finalizers and exact finite objective

Let c be core cost, n the number of factors, m the number of ordinary
comparisons, and g the number of nonempty disjoint factor groups. If G_j is
a group product and R_i an ordinary residual, the only allowed finalizers are

```
SOS:    sum_i R_i^2 + sum_j (G_j-1)^2;
anchor: G_a*(1+sum_i R_i^2+sum_{j!=a}(G_j-1)^2)-1.
```

Literal source cost for either form is

```
c+n+3m-1+2g,
```

except the empty-SOS case m=0,g=1 with an anchor, which is simply the factor
product minus1 and costs c+n. Each comparison residual, square, sum, addition
of1, anchor multiplication and final subtraction is paid. The accompanying
comparison-system ledger costs c+n−g and has m+g comparisons.

For factor weights w_i, maximum ordinary residual bound r, and group sums d_j,
the precise optimization objective is

```
SOS:    2 max(r,d_0,...,d_(g-1));
anchor: d_a + 2 max(r, all d_j with j!=a).
```

The search authenticates the earlier [reviewed minimax subset routine](neary_woods_universal_joint_and_coupled_partitions.md)
and extracts only its `optimal_partitions` function through Python AST. Its
module imports, builders, census and verification code are never executed.
For each possible group count, the routine minimizes the maximum group sum
using every first block containing the least remaining factor. Greedy
partitions supply upper bounds; largest-weight and average bounds prune only
impossible improvements. It then considers every nonempty distinguished
anchor subset as well as all-SOS. Thus every partition and every allowed
finalizer is represented. New source-derived weights are supplied afresh.

A separate restricted-growth enumeration checks the routine on14 small
instances through seven factors, covering2,310 partitions. This is a focused
implementation cross-check, not the basis of the complete finite optimality
proof. The source receipts retain all120 group-count optima and their subset
search statistics, each emitted at both interfaces.

There is also a short exact floor certificate independent of the group-count
search. Sort weights in descending order, and write w_(n+1)=0. The minimum
over all possible group counts equals

```
min(2*max(r,w_1),
    min_{1<=k<=n}(sum_{i<=k} w_i + 2*max(r,w_(k+1)))).
```

All singleton SOS groups attain the first candidate. If an anchor omits a
largest weight, its positive contribution makes it worse than that candidate.
Otherwise, take its longest initial prefix of sorted weights. Moving every
other anchor weight into a singleton group cannot increase the objective:
the first omitted weight was already a lower bound on the other-group peak.
The prefix anchor with singleton remaining groups attains the corresponding
candidate. Tied weights cannot improve by being partly included. The code
uses the equivalent threshold sum over weights strictly above each threshold.
This proves312 for the four ordinary-joint bases and688 for the four normalized
joint bases, and the emitted optima attain these floors.

## Full positive-zero correspondence and signed pullbacks

The [independent all-sixteen tail theorem](review_neary_woods_tail_quotient_math.md)
proves positive restoration before invoking the old compiler theorem. With
Z0=(q−1)F3 and the unchanged packing quotient S, the formal inverse is

```
beta_parent = beta_child + Z0 - S.
```

Both offsets are beta-independent. At every tuple the changed sum satisfies
`(beta_child+Z0-S)+S=beta_child+Z0`. The new packet checks the sole consumer
conditions and this complete graph identity for every canonical source and
every regrouped source, including its full finalizer:4,102 canonical and
64,918 regrouped register identities. At120 diagnostic values, including30
rational tuples, it also evaluates the complete regrouped parent and child
polynomials and reconstructs their finalizers independently. These evaluations
do not substitute for the algebraic induction or the positive-zero theorem.

Regrouping itself preserves the full supplied positive zero set within each
fixed base on a valid program slice. An integer zero of either finalizer
forces every ordinary residual to0 and every group product to1; for the
anchor, its second factor is a positive integer, so both factors equal1.
Multiplying the group equations gives the canonical product equation. The
reviewed complete tail theorem then restores the positive parent beta and
forces every individual native and outer factor to+1. Every other grouping
therefore vanishes. Conversely, all individual factors+1 and ordinary
residuals0 satisfy every emitted finalizer.

Only beta changes between tail parent and child. Its inverse may be negative
off the zero set; no whole-orthant bijection is asserted. Changing the native
strong/scale treatment between different bases preserves the represented
relation through its inherited witness extensions; their private witness
tuples are not identified with each other.

## Combining the unchanged sources

The older [sixteen-base partition receipt](neary_woods_universal_product_scale_partitions.md)
also contains eight joint-unprojected bases. Their complete sources and
minima remain unchanged. Reading their frozen minima and combining them with
the eight freshly optimized bases yields the following known finite-family
catalogue, with degree upper bounds:

```
253/982,255/848,256/802,257/604,258/558,259/404,260/398,261/312,
263/302,264/272,265/228,266/212.
```

The first eight points have43 positive witnesses; the final four have44.
The unrestricted endpoint266/212 survives unchanged, as does the entire
45-witness stratum. Within the combined44-witness stratum the catalogue is

```
257/975,258/837,259/601,260/555,261/454,262/398,
263/302,264/272,265/228,266/212.
```

Those retained historical points are authenticated previous results, not
newly replayed source arrays. This distinction is explicit in the receipt.
No conclusion about other compiler bases, different finalizers or arbitrary
Diophantine encodings follows from the finite optimum.

## Reproduction

The bounded standard-library CLI exposes no mutable source-packet interface:

```
python3 neary_woods_universal_tail_partitions.py --root PATH_TO_WIP \
  --expect neary_woods_universal_tail_partitions.json
```

`--output PATH` writes the deterministic receipt. All source/proof dependencies
are pinned before use, and optimized Python is rejected. The all16 transfer
and fixed numeral recipes are compared literally; every emitted source is
closed, acyclic, fully live and uses all declared coordinates and numeral
roles. Author construction and exact receipt replay pass. Independent weighted
and full source reviews are separate artifacts; this note records the author
stage without claiming their completion.
