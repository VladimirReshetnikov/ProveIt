# Role-weighted rank-ULC for the mixed-sign Gallai–Edmonds a=2 branch

Status: the exact package passes a separately implemented local checker; an external-agent audit is in progress. No claim of a new literature theorem is made here.

## Statement and dependencies

Let P be a finite preorder of comparability matching number at most three. Suppose its Gallai–Edmonds reduction has attachment set A={i,j}, a residual core K of at most five vertices containing A, and an independent exterior whose vertices have neighbors only in A. Assume that every exterior edge at i points from i to the exterior, while every exterior edge at j points from the exterior to j. The dual configuration is included by exchanging names. Give every vertex positive independent tail/head activities u_v,v_v. Then its disjoint-support gamma sequence is ultra-log-concave with respect to its actual degree.

Here gamma_k is the sum of u_T v_H over ordered disjoint k-subsets (T,H) admitting a bijection along off-diagonal preorder arcs. A feasible support is counted once, regardless of how many witnessing bijections it has. The actual degree at strictly positive activities is the matching number of the underlying undirected comparability graph. The degree-at-most-two cases follow from the universal weighted first-gap theorem. At actual degree three, the first Newton inequality is universal and the remaining assertion is gamma_2^2 >= 3 gamma_1 gamma_3.

The finite GE core reduction and completeness of the 1,084 two-attachment structural templates are inputs from `../preorder-gamma-degree3/THEOREM_SYNTHESIS.md` and the independently audited catalog `../preorder-gamma-degree3/two-attachment/templates.json`. We use all 494 catalog templates with opposite attachment signs, including harmless overcoverage. Other inputs are the independently audited weighted theorem for all preorders on at most six vertices (`SIX_VERTEX_ROLE_ULC.md`) and the established weighted bipartite matching-rank-at-most-four theorem (`../matching-rank-four-result/matching-rank-four.tex`, Theorem `thm:main`).

## Exact arbitrary-population compression

Partition the exterior into head-only vertices adjacent to i, tail-only vertices adjacent to j, and shared vertices with i -> s -> j. Put

H = sum of v_s over exterior vertices adjacent to i,
T = sum of u_s over exterior vertices adjacent to j,
W = sum of u_s v_s over shared exterior vertices.

Write Gamma_L(z) for the role-weighted support polynomial of an induced core L. Then the exact identity is

Gamma_P = Gamma_K
          + T v_j z Gamma_(K-j)
          + H u_i z Gamma_(K-i)
          + (HT-W) u_i v_j z^2 Gamma_(K-{i,j}).

Proof: a support uses zero, one, or two exterior vertices. If an exterior vertex is a tail, its matched head is forced to be j; if it is a head, its matched tail is forced to be i. No support can use two exterior tails or two exterior heads. Removing these forced endpoint pairs gives the indicated core support, bijectively at the level of endpoint supports. In the two-exterior case the chosen tail and head must be distinct physical vertices; summing their weights gives HT-W. Thus no multiplicity of matching witnesses is introduced.

All summaries are nonnegative and W<=HT, since every summand u_s v_s of W occurs in the product HT. If the shared type is legal, both singleton types are legal: remove respectively the incoming or outgoing edge of a shared exterior vertex. The remaining relation is transitive, because that vertex now has no incoming or no outgoing arcs; all paths using only core vertices are unchanged. Equivalently, the finite verifier recomputes legality directly for all three possible types.

If the shared type is legal and T>0, replace the entire exterior by two vertices:

- one shared vertex s with u_s=T and v_s=W/T;
- one head-only vertex h adjacent to i with v_h=H-W/T.

The unused activity u_h can be any positive number. The new summaries are exactly H,T,W. Hence its support polynomial equals the original polynomial. If T=0, then W=0; use u_s=v_s=0 and v_h=H. If the shared type is not legal, compress the two singleton classes independently by summing their relevant activities. Absent legal types are omitted.

The replacement has at most two exterior vertices and therefore at most seven vertices altogether. Some effective activities can be zero. This is allowed in the polynomial identities and closed-orthant certificates, or by taking positive limits. We do not assert that effective activities stay strictly positive. We also do not infer actual-degree-three normalization merely by padding a lower-degree sequence: original degree at most two is settled first by its own inequality, and original degree three is treated by the cubic inequality whose support polynomial is preserved exactly.

## Finite closure of the compressed cases

`a2_mixed_compression_targets.json` lists all 494 mixed-sign source templates, their exact compressed rows, structural justification, and any target reference. The cases are:

- 366 compressed preorders on at most six vertices;
- 19 of matching number at most two;
- 49 disconnected cases, reduced to at-most-six-vertex components or lower-rank components;
- 3 connected bipartite cases;
- 57 seven-vertex, connected, nonbipartite, nontotal cases, covered by 56 distinct exact certificate targets.

For a disconnected case the support polynomial is the product over connected components. Products of rank-ULC nonnegative sequences are rank-ULC (equivalently, convolution preserves binomial-normalized log-concavity). Alternatively, when all component ranks are at most two they have negative-real-rooted support polynomials and the product does as well. A rank-three connected component in a seven-vertex disconnected graph has at most six vertices and any remaining components have rank zero.

The 56 target files are `nontotal7_certificates/t%03d.json` at the IDs in the manifest's `unique_nontotal7_targets` list. Each gives an exact identity

G(u,v) = gamma_2^2 - 3 gamma_1 gamma_3
       = sum_l q_l m_l(u,v) h_l(u,v)^2 + R(u,v),

where q_l are positive rationals, m_l are monomials with nonnegative integer exponents, and R has nonnegative rational coefficients. Hence G>=0 on the full nonnegative orthant. Relabeling transports activities with vertices, and order duality exchanges tail and head activities. The manifest has 57 target references; the checker establishes each required relabeling or duality by independently searching all seven-vertex permutations.

## Reproduction and audit boundary

Run `python verify_a2_mixed.py` from this directory. It uses only the Python standard library and does not import the certificate producer or the enumeration canonicalizer. It independently enumerates endpoint supports by Hall's criterion, verifies all 56 exact rational identities, checks the four-term forced-endpoint formula symbolically for every source template, recomputes all legal exterior types, checks all compressed structural branches, and checks target isomorphisms by direct permutation comparison.

The receipt `a2_mixed_complete_verification.json` reports:

- 56 rational target identities, with 1,135 square terms and 6,445 positive remainder terms;
- 494 symbolic forced-endpoint identities and 494 structural branch checks;
- 1,482 exact-rational compression comparisons, including 103 zero effective-head boundary tests;
- 57 target isomorphism checks.

The finite symbolic tests supplement the arbitrary-population forced-endpoint proof; they do not replace it. The source catalog and manifest SHA-256 hashes are pinned in the receipt. Catalog completeness and the GE bound remain explicit prior dependencies. Same-sign a=2, the remaining a=1 and a=3 branches, and arbitrary non-total degree-three preorders in general are not claimed by this note.
