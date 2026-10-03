# Independent weighted partition minima for the eight U9 tail bases

**PASS.** A separate threshold bin-packing algorithm and analytical anchor bounds confirm all120 exact minima for every group count in the eight authenticated tail bases. Both duration interfaces have the same weighted task. All120 frozen author plans attain these independently computed minima. The43-witness frontier is

\[
 (253,982),(255,848),(256,802),(257,604),
 (258,558),(259,404),(260,398),(261,312).
\]

The pairs are complete operations and propagated degree upper bound. This review proves exact minima of that **finite weighted objective**, not exact polynomial degrees, unrestricted arithmetic lower bounds, or a new universal input theorem. The complete source/API audit of the emitted partition schedules is separate.

The [checker](review_u9_tail_weighted_minima.py) and [receipt](review_u9_tail_weighted_minima.json) pin the [all-sixteen source packet](neary_woods_tail_quotient_all16.md), from which weights, ordinary residual bounds, witness counts and paid core sizes are read. The two duration interfaces are checked to have identical weighted data. The frozen [partition author packet](neary_woods_universal_tail_partitions.md) is separately authenticated and its120 plans compared only after the independent minima have been computed. No author optimizer, author verifier, AST-isolated optimizer, or historical source is imported or executed.

## Exact analytical floor over all group counts

Let positive factor weights be sorted as `w1>=...>=wn>0`, let r be the maximum ordinary residual degree bound, and let a partition have group sums `s1,...,sg`. Its two finalizer objectives are

\[
 D_{SOS}=2\max(r,s_1,\ldots,s_g),
\]

\[
 D_{anchor}=s_a+2\max(r,s_1,\ldots,\widehat{s_a},\ldots,s_g).
\]

Set `w[n+1]=0`. The **exact** minimum when all group counts are allowed in this family is

\[
 \boxed{\min\left\{2\max(r,w_1),\ 
 \min_{1\le k\le n}\left(\sum_{i=1}^{k}w_i+
                      2\max(r,w_{k+1})\right)\right\}.}       \tag{1}
\]

The first candidate is attained by all-SOS singleton groups. An anchor omitting the first largest item cannot improve it: a nonanchor group already contains that item, and the positive anchor adds to twice that lower bound. Otherwise, let k be the length of the initial sorted prefix contained in the anchor, stopping immediately before its first omitted item. Remove any later items from the anchor and put them in singleton nonanchor groups; also split all other nonanchor groups. This cannot increase the maximum nonanchor weight or the anchor weight. The resulting objective is the kth candidate in(1). If nothing is omitted, k=n. Conversely every prefix candidate is realized by that prefix as anchor and all remaining items as singletons. Ties among item weights do not affect this argument.

It is generally insufficient to consider only the largest anchor item or only its residual floor. For example weights `(100,60,1)` with `r=0` have floor161, attained by the entire prefix as the sole anchor; the singleton-SOS value is200 and the singleton-largest anchor value is220. Formula(1) handles both this phenomenon and the actual tail data.

For the eight tail bases, the exact floors are

\[
 (312,312,312,312,688,688,688,688).
\]

They are all attained by singleton SOS partitions, and already by the much smaller group counts recorded below. The earlier expression using `wmax+2r` alone was only a lower bound; the frozen author now uses the exact prefix formula.

## Every fixed group count is independently certified

Let W be the sum of all weights and `wmin` their minimum. The checker does not reproduce the author's subset-partition minimax recurrence. It assigns items in descending order into bins, storing only the sorted current bin loads. Equal-load bins are symmetric. At each state it tries every distinct load able to receive the next item. Memoization therefore removes only equivalent load states, not possible packings. The procedure gives an exact capacity-feasibility decision and reconstructs an actual packing when successful.

For these eight concrete weighted tasks:

- **One group:** there are only two choices, with objectives `2max(r,W)` and `W+2r`. The latter wins in each actual base.
- **Two groups:** every SOS partition has bound at least `2max(r,wmax,ceil(W/2))`. The checker finds a packing attaining it. If one of the two groups is an anchor, its objective is at least `W+wmin`, because its nonempty complement has weight at least wmin. That bound is larger than the attained SOS value in every base.
- **Three groups:** binary search with the independent bin-placement decision finds the exact smallest SOS capacity. The checker also explicitly rejects the capacity one lower. For an anchor, the larger of the two remaining group sums is at least half their total, so the anchored objective is at least W. Every attained SOS value is no larger than W; anchors cannot improve it.
- **Four through n groups:** a four-bin SOS packing attains the analytical floor(1) in every base. Splitting any non-singleton group until exactly the desired number of groups is reached preserves its capacity. Since no partition can beat(1), this certifies every remaining group count.

There is also a short direct obstruction behind the only nontrivial three-bin thresholds: the ordinary-joint bases contain weights `156,138,78,61,61`. With capacity198, the156 and138 must occupy separate bins, and neither can share with any of78,61,61. Those last three total200, exceeding the third bin's capacity. Thus capacity at least199 is necessary. Base3 additionally has total604, forcing capacity at least202. The independent bin solver finds attaining packings.

The complete results, for each of the two duration interfaces, are:

| Base | W | r | One group | Two groups | Three groups | Every group count from4 to n |
|---|---:|---:|---:|---:|---:|---:|
|0|551|122|795|552|398|312|
|1|558|122|802|558|398|312|
|2|593|122|837|594|398|312|
|3|604|122|848|604|404|312|
|4|929|14|957|930|688|688|
|5|936|14|964|936|688|688|
|6|971|2|975|972|688|688|
|7|982|0|982|982|688|688|

The factor counts are14,14,15,15,15,15,16,16, giving120 distinct `(base,group-count)` tasks. Independent attaining partitions for all120 are saved in the receipt. They need not match the author's tie-breaking choices; their objective values do match.

## Costs and frontier scope

For a fixed base with paid core C, n factors, m ordinary comparisons and g nonempty groups, the literal regrouping schedule has

\[
 C+n+3m+2g-1
\]

operations. There are `n-g` group multiplications. With an all-SOS finalizer, the `m+g` residuals cost three operations each except the first needs no running-sum addition. With an anchor and at least one remaining residual, its omitted square/subtraction is exchanged for the paid `1+SOS`, anchor multiplication and final subtraction, giving the same total. The special empty-SOS case `m=0,g=1` costs `C+n`, one less, because its finalizer is simply the product minus1.

The checker uses these formulas with the authenticated paid core counts and independently reconstructs the43- and44-witness frontiers. The claimed43-witness frontier at the start of this note matches all eight points. This is a frontier within the eight tail bases and this literal grouping/finalizer grammar. Historical joint-unprojected bases, algebraic rewrites, alternative coordinate changes and other circuit optimizers are outside this independent search.

The weights themselves are upper bounds on full source polynomials, with all supplied program parameters counted as variables of degree1 and fixed compiler numeral recipes of degree0. Optimizing those weights does not convert them into exact degrees. The fixed-source positive-zero theorem and unbounded input language are inherited from the separately reviewed source packets, not proved by bin packing.

## Reproduction and comparison

The source pins the all-sixteen source trio and the frozen author partition trio. The latter is read as data only. All120 author partitions are checked for complete disjoint coverage, group count, attaining objective, operation count and witness count against the independently computed optima. The author source's own algorithm is not run.

Seven small independent Bell-enumeration examples validate the analytical floor, including multi-item anchors, tied weights and residual-dominated cases. Independent exhaustive labeled-bin assignments check the capacity procedure on those same small examples. The full-size evidence is the exact bin decision plus the analytical lower certificates above, not a small-case extrapolation.

```
python3 review_u9_tail_weighted_minima.py --root PATH_CONTAINING_PINNED_TRIOS \
  --expect review_u9_tail_weighted_minima.json
```

`--output PATH` writes the deterministic receipt; comparison is recursively type-exact and `python -O` is rejected. Writer and fresh replay from `/` pass. No repository file, frozen source or Git state is modified.
