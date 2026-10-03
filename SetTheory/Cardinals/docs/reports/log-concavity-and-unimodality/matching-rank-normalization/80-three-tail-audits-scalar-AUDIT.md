# Independent approval: the sharp weighted bipartite rank threshold

Approved October 1, 2026, at16:08 UTC. The exact submitted source and independent checker are pinned in approval.json. The source's historical pending-review sentence is superseded by this approval.

## Exact support formula and rank

The four vertex sets are disjoint. For selected core cardinalities i,j at total support size k, the outside-left population is k−i and outside-right population k−j. Necessity requires k−i≤j and k−j≤i, both equivalent to i+j≥k. Sufficiency matches outside-left vertices into the selected right core and outside-right vertices from the selected left core, leaving exactly i+j−k unused vertices on each selected core shore. Their complete bipartite core matches them. Hence the binomial quota formula counts endpoint pairs once, irrespective of witnesses.

An independent literal Hall test reconstructs all78 quota graphs for p=q=3 and k≤6 and checks all subsets of their selected left vertices. Exactly30 quota patterns are feasible, precisely those satisfying the displayed inequality. The cover P union Q gives rank at most p+q. When exterior sizes are at least q,p respectively, disjoint matchings of the core shores into opposite exterior populations give rank at least p+q. Positive activities preserve this actual degree.

## Counterexample and exact parameter identity

The independent standard-library checker reconstructs every coefficient from the quota formula, rather than importing a producer polynomial. For N40,lambda10000 it verifies both the full coefficients and the scaled sequence

    [1,90240,907219080,1024191381360,161879846800,6130238400,97614400].

The last scaled Newton gap is exactly−1722535205514240000. The unscaled gap is exactly−172253520551424 times10^44. The preceding four gaps are positive. The graph has86 vertices and249 edges.

The checker also independently multiplies univariate rational coefficient dictionaries to prove the full N,lambda factorization in the note. Its leading coefficient−N²+34N−49 is negative for integers N≥33 and nonnegative for3≤N≤32. Both other coefficients are positive for N≥3. No minimum-vertex claim follows.

For N33,lambda30000, it verifies the72-vertex/207-edge variant, all seven scaled coefficients and last gap−38842940605759488. Positive variable rescaling changes every corresponding Newton gap by a positive factor and therefore preserves its sign.

## Every higher rank and sharpness

For any fixed p,q≥3, the degree p+q terms in core activity come only from selecting every core vertex. The three top coefficients therefore have the exact leading terms stated in the source. First choose sufficiently large finite integer exterior sizes, each at least the size of the opposite core shore, so that their finite binomial ratio is below2d/(d−1). This is possible because its limit is pq/((p−1)(q−1)), and

    (d+1)pq−2d(d−1) ≥ d²−4d−9 >0  for d≥6.

Then choose a sufficiently large finite positive integer core activity. The ratio of the full coefficients tends to that finite-population leading ratio, so the strict violation persists. The actual degree remains d by the previously checked matching. Taking p3,q=d−3 supplies every integer d≥6. The order of the two finite choices is correct; no inference from floating-point sampling is used.

The positive direction through rank five is exactly Corollary5.2 of the separately approved unrestricted two-element matroid paper. Its frozen ZIP is an explicit dependency of the forthcoming package. Thus the universal weighted bipartite matching-rank threshold is five. The negative examples already use one positive activity per physical vertex. Orienting every edge from the left shore to the right shore gives a height-two strict order; adding reflexive pairs does not affect disjoint-endpoint supports. No unweighted failure or failure of every graph at rank six is inferred.

## Scope and intake overlap

Root subsequently verified that the new main intake at commit1512ef8356d10fef99e7caaa2753620f0c900c83 already contains the same weighted rank-five guarantee and all-higher-rank negative construction in ProveIt_Weighted_Rank_Five_and_Two_Shore_Covers. The independently inspected negative_ranks.tex includes the same quota formula and a sharper N33,weight26804 example. Accordingly this audit is an independent reconstruction and exact verification, not a new-to-intake or literature-priority claim. The integrated paper should disclose that overlap. No external publication or repository modification is authorized or performed by this audit.
