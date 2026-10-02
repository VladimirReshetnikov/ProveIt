# Exact result: arbitrary role-weighted preorders on at most six vertices

## Statement

For every finite preorder on at most six vertices, assign arbitrary strictly positive tail/head activities u_i,v_i and count each feasible ordered pair of disjoint endpoint supports once with weight u_A v_B. The resulting coefficient sequence is ultra-log-concave when normalized by its actual degree.

The new finite certificates below have passed both a separately implemented local exact checker and an external-agent audit. The external checker verified all 223 exact identities, all 7,090 quotient/block configurations and all 3,059 relevant cases, the declared multiplicities, 321,120 permutation/duality actions, and Hall-versus-bijection support checks. See `../preorder-nontotal-independent-audit/n6/receipt.json`.

## Structural reduction

The actual degree is the matching number of the undirected comparability graph. For n<=5 it is at most two, so weighted Motzkin–Straus supplies the complete claim. At n=6 only actual degree three remains, and the first cubic Newton inequality is again universal. We need gamma_2^2>=3 gamma_1 gamma_3.

- If the comparability graph is disconnected and has matching number three, every nontrivial component has matching number at most two. Each component's weighted support polynomial is real-rooted by the first-gap theorem, and disjoint component polynomials multiply. Thus the product is real-rooted and rank-ULC.
- If the graph is connected and bipartite, transitivity prevents any directed path of length two through three distinct vertices, since that would create a triangle. A nontrivial equivalence pair cannot have another neighbor in a connected bipartite component, because equivalent vertices have the same neighbors and would create a triangle. Hence this six-vertex case is a height-two poset, with all tails on one shore and all heads on the other. The role weights reduce exactly to ordinary positive vertex activities u_i on the lower shore and v_j on the upper shore. The established weighted bipartite matching-rank-at-most-four theorem applies; only its rank-three portion is needed.
- Total preorders are covered by the independently approved role-weighted total-preorder theorem.
- It remains to check connected nonbipartite, nontotal six-vertex preorders of matching rank three.

The bipartite input is explicitly a dependency: `../matching-rank-four-result/matching-rank-four.tex`, Theorem `thm:main` (Actual-degree normalization through rank four), with its README and exact checkers. No new proof of that prior theorem is claimed in this file.

## Complete finite certificate range

Every preorder is an expansion of its quotient poset by positive equivalence-class sizes. Choosing a linear extension of the quotient allows all its strict arcs to point forward. Enumerating every naturally labeled quotient poset and every positive ordered composition of six gives 7,090 redundant configurations, covering every six-vertex preorder up to relabeling.

The structural branches divide these configurations as follows:

- 3,183 have matching number at most two
- 515 are disconnected with matching number three
- 301 are connected bipartite with matching number three
- 32 are total with matching number three
- 3,059 are connected, nonbipartite, nontotal, with matching number three

The final branch has 223 types up to vertex permutation and order duality. The exact certificate search succeeded for every type. All activities remain independent variables, so these symmetries impose no restrictions on weights.

## Nonnegative identity form

For each type, with w=(u_1,...,u_6,v_1,...,v_6), the certificate expresses

    gamma_2(w)^2-3 gamma_1(w) gamma_3(w)
      = sum_l q_l w^m_l (sum_a c_(l,a) w^a)^2 + sum_e r_e w^e,

where q_l>0 and r_e>=0 are rational, every exponent is a nonnegative integer, and all expansion terms have bidegree (4,4) in tails and heads. The 223 consolidated certificates contain 586 square terms and 31,094 positive remainder monomials.

As in the total-preorder proof, numerical LP output was only a proposal. Final coefficients were reconstructed over the rationals, and the complete identity was checked exactly. A failed numerical SOS search would not have constituted a counterexample; there are no failures in this six-vertex range.

## Independent exact audit

`audit_nontotal6.py` imports no producer or earlier verifier. It independently:

1. Enumerates every candidate ordered disjoint support for each target, compares Hall's criterion with explicit matching bijections, and reconstructs the role-variable coefficient polynomials.
2. Checks all 223 rational identities exactly, including activity dimensions, exponent nonnegativity, multiplier signs, bidegrees, and nonnegative remainders.
3. Expands the complete vertex-permutation and order-dual orbits of the certified representatives.
4. Regenerates all quotient posets by a different forward-arc-mask/transitivity generator and all positive block compositions by cut positions. It independently classifies all 7,090 configurations and confirms that every one of the 3,059 cases in the remaining branch lies in a checked orbit.

All 31,220 Hall-versus-matching candidate checks and every coverage check passed. The independent forward-mask quotient counts are 1,2,7,40,357,4824, agreeing with the complete naturally labeled quotient range.

Files:

- `nontotal6_templates.json`: the 223 representatives and redundant-configuration multiplicities
- `nontotal6_certificates/t000.json` through `t222.json`: exact rational identities
- `audit_nontotal6.py`: independent standard-library audit
- `nontotal6_complete_verification.json`: coverage, exact-identity checks, and certificate hashes
- `enumerate_nontotal6.py`, `certify_nontotal6.py`: production enumeration and certificate proposal code

Run `python audit_nontotal6.py` with standard Python. The universal first-gap proof, total-preorder theorem, and established bipartite theorem complete the other branches mathematically.

## Limits

This establishes the weighted claim for arbitrary preorders through six vertices. It does not yet establish arbitrary weighted preorders on seven vertices or unbounded-size preorders of actual degree three. No general weighted real-rootedness or worldwide novelty claim is made. The seven-vertex connected nonbipartite nontotal range is the next finite target.
