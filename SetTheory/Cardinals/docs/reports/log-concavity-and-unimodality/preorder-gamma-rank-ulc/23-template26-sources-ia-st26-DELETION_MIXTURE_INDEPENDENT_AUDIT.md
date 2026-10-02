# Independent audit: single-arc three-core deletion mixtures

Approved 2026-10-01. Scope: the deletion-mixture lemma and its ten exact integer-population cross identities. This does not by itself assert a replacement proof of the complete template26 last gap, and does not modify the frozen degree-four release.

## Mathematical review

The core is the three vertices 0,1,2 with the sole internal arc 2→0. Exterior vertices are pure tails with neighborhoods 1,2,3,5,7. These are precisely the five nonempty subsets of the three core vertices closed under the implication 2→0. The resulting relation is a preorder after adding its diagonal. Every feasible exterior vertex occupies a tail role and requires a distinct core head, so at most three exterior vertices can appear in a support. The fixed arc ensures that the linear coefficient A of each available deletion polynomial is at least one.

For a nonzero mixture, let A=Σw_i A_i>0 and λ_i=w_i A_i/A. Then (B/A,T/A)=Σλ_i(B_i/A_i,T_i/A_i). At a fixed horizontal coordinate, the maximal vertical coordinate in this finite convex hull is attained by a mixture supported on at most two points. For completeness, choose a maximizing mixture with minimal positive support. If at least three coefficients are positive, there is a nonzero perturbation δ satisfying Σδ_i=Σδ_i x_i=0. Both small signs of the perturbation are feasible; optimality forces Σδ_i y_i=0. Increase its magnitude until one coefficient reaches zero, contradicting minimal support. This also covers repeated horizontal coordinates. Consequently, checking every segment (including its endpoints) below y=x²/3 proves the entire hull lies below it. This is not an assertion that the subgraph of a convex parabola is itself convex.

For a marked exterior vertex, its support activity t∈[0,1] gives exactly tQ(m)+(1−t)Q(m−e_i), since supports contain that physical vertex at most once. The pinned, independently approved single-vertex-weighted degree-at-most-three theorem therefore supplies the last Newton inequality along all five such segments. At surviving degree three its normalization is B²≥3AT; if surviving degree is at most two, T=0 and this particular order-three inequality is automatic. Positive rescaling covers arbitrary nonnegative weights on each two-point segment. No independent-role-weighted theorem is used here.

For distinct available deletion types i,j, both populations are positive. Set m=x+e_i+e_j, x∈N⁵. The two deletion polynomials are Q(x+e_j) and Q(x+e_i). The exact cross identities prove 2B_iB_j−3(A_iT_j+A_jT_i)≥0. Together with the endpoint gaps this proves every nonnegative two-term mixture. Deletions of distinct physical vertices of the same type give identical polynomials, so no further pair is missing. Combined with the preceding convex-hull argument, this establishes every nonnegative mixture of Q and the available one-vertex deletions, including the zero mixture.

The claim is restricted to integer clone populations. Mixture weights may be arbitrary nonnegative real numbers. Only the last order-three Newton inequality is concluded; neither a full Lorentzian property nor real-rootedness nor arbitrary independently weighted exterior populations follows from this argument.

## Independent algebra

`audit_deletion_mixture.py` uses only the Python standard library and imports no producer code. It constructs the coefficients by direct disjoint-tail/head Hall feasibility, counting each ordered endpoint support exactly once, with all selected exterior clones mandatory. All 56 quota vectors of total at most three are enumerated; larger quotas are excluded by the core-head bound. All 42 nonzero coefficients agree exactly with the stated A,B,T formulas.

The checker reconstructs each cross target directly from that Hall kernel. It validates all ten unordered type pairs and their exact shifts, every exponent's nonnegative integer domain, all rational weights and all positive remainder coefficients. Binomial multiplication constants are counted independently as ordered pairs of subsets with a specified full union, rather than copied from a producer multiplication routine. Full coefficient identities hold for all ten certificates, containing 196 positive rational squares and 846 positive binomial remainder terms.

The degree-three theorem source hash is checked against its independent approval receipt. The algebra receipt pins the proof, certificate, checker, theorem source and dependency receipt. A source status sentence predating the theorem's approval does not supersede its later explicit independent approval receipt.

Reproduce with:

    python3 audit_deletion_mixture.py

Files: `deletion_mixture_algebra_receipt.json` and `deletion_mixture_approval_receipt.json`.
