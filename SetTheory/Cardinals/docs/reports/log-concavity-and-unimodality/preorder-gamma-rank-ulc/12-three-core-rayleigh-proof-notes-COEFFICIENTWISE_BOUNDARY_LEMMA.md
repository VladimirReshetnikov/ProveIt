# Coefficientwise boundary Rayleigh inequalities for an oriented three-core bipartite graph

Status: proposed computer-assisted all-size lemma, October 1, 2026; independent audit requested. The released bipartite-and-pendant paper and package are unchanged.

## Statement and exact definitions

Let D be a loopless directed relation with physical bipartition V=C disjoint-union I, where C={0,1,2}. Every arc crosses the partition; arbitrary opposite arcs are allowed. Work in the polynomial ring in independent commuting variables u_v,v_v, the tail and head activities of every physical vertex. Feasible supports are ordered disjoint endpoint pairs admitting a directed perfect matching, counted once, with weight u^S v^T.

For i,j,k distinct in C, let

- a_i be the sum of weights of size-one supports whose used core set is {i};
- b_ij be the sum of weights of size-two supports whose used core set is {i,j};
- c be the sum of weights of size-three supports, whose used core set is all of C.

The proposed assertion is

    b_ij b_ik - a_i c >=_coeff 0.

Here coefficientwise nonnegative means every coefficient in the original independent u_v,v_v variables is a nonnegative integer. The core activities are included in a_i,b_ij,c; they are not factored out or identified.

The associated physical orientation-support polynomial, after retaining only core monomer variables, is

    z_0 z_1 z_2 + sum_i a_i z_j z_k + sum_(i<j) b_ij z_k + c.

The inequality is its Rayleigh difference in z_j,z_k evaluated at z_0=z_1=z_2=0. Ordinary Lorentzianity alone does not establish this stronger coefficientwise assertion.

## Why the verification localizes to at most four exterior vertices

Fix i=0,j=1,k=2 by relabeling. Every monomial in either b_01 b_02 or a_0 c has total degree eight in the role activities. Its physical core multiplicities are 2 at 0 and 1 at each of 1,2. Its total exterior degree is four.

A potentially negative coefficient must occur in a_0 c. The a_0 factor uses one exterior vertex, while c uses three distinct physical exterior vertices. Therefore the union of exterior vertices has one of exactly two patterns:

1. Four distinct vertices, all with physical multiplicity one
2. Three distinct vertices, with physical multiplicities 2,1,1

Every monomial with any other exterior multiplicity pattern has coefficient zero in a_0 c, so its gap coefficient is automatically nonnegative. For a given monomial, arcs incident to exterior vertices not appearing in it cannot affect its coefficient. Restricting to the three core vertices and those three or four exterior vertices therefore preserves the coefficient exactly.

Further, an arc whose tail or head role variable does not occur in the fixed monomial can never occur in a support contributing to that coefficient. Deleting every such arc also preserves the coefficient. The remaining graph depends on a bounded list of relevant directed arc bits.

## Complete role-monomial classification

Use role bit 1 for tail and 0 for head. At doubled core vertex 0, let c_i in {0,1,2} be the exponent of u_0, so its v_0 exponent is 2-c_i. The two occurrences of vertex 0 in a product of supports have role allocations

    c_i=0: (0,0)
    c_i=1: (0,1) or (1,0)
    c_i=2: (1,1).

Vertices 1 and 2 have fixed role bits j,k in {0,1}. This gives 3*2*2=12 core-role patterns. Total tail degree is four in each product: b*b has two size-two supports, and a*c has sizes one and three.

### Four exterior vertices

Every exterior vertex has a fixed role bit. The number of exterior tails must be

    4-c_i-j-k.

This lies between zero and four. Up to relabeling exterior vertices, we may put that many tail roles first and then the head roles. Thus there are exactly 12 role-monomial cases here. For each case, retain every possible cross-partition directed arc compatible with a role that occurs in the monomial; there are at most 12 such arcs. Enumerating all their subsets gives 11,392 graph cases in total.

### Three exterior vertices

Label the repeated physical exterior vertex 0 and the other two 1,2. Let e_i in {0,1,2} be its tail exponent and e_j,e_k in {0,1} the roles of the other two. Retain exactly the tuples satisfying

    c_i+j+k+e_i+e_j+e_k=4.

There are 36 tuples after the core-role patterns are included. At most ten compatible directed arcs occur. Exhaustively enumerating their subsets gives 5,984 graph cases.

Both orientations of the same physical edge can be relevant only when both endpoint role types occur in the monomial. The checker keeps these as separate directed bits. No loop is possible because the physical core and exterior parts are disjoint.

The total is therefore 48 role-monomial cases and 17,376 exact graph cases.

## Exact coefficient computation in each graph

The checker computes a support-feasibility predicate by listing the at most six bijections between its selected core and exterior sets. It returns true if at least one bijection consists of present, role-compatible arcs. It does not count how many bijections succeed.

For four exterior vertices:

- To obtain the positive coefficient, choose the two exterior vertices assigned to b_01 (six choices), assign the remaining two to b_02, and sum over the distinct role allocations at doubled core vertex 0. Count the term if both supports are feasible
- To obtain the negative coefficient, choose the one exterior vertex in a_0 (four choices), put the remaining three in c, and sum over the distinct core-0 role allocations. Again use Boolean feasibility for each factor

For three exterior vertices:

- Both positive factors must contain the repeated exterior vertex. Choose which single exterior vertex accompanies it in b_01 (two choices); the other accompanies it in b_02. Sum over distinct role allocations at doubled core 0 and at the doubled exterior vertex
- In a_0 c, the singleton exterior of a_0 must be the repeated vertex. The c factor contains all three exterior vertices. Sum over the same role allocations

Each choice specifies an ordered pair of feasible endpoint supports in the corresponding product, uniquely. Identical-role occurrences have only one allocation, while mixed-role occurrences have two; there are no factorial or matching-witness multiplicities. Thus subtracting the two integer counts gives exactly the fixed monomial coefficient.

## Verification outcome and certificate files

`universal_boundary_check.py` implements the complete classification and coefficient calculation. It uses only the Python standard library. Its receipt `universal_boundary_receipt.json` records the role types, number of compatible arcs, graph count, and coefficient histogram for every case.

All 17,376 graph cases passed. Every computed coefficient is one of 0,1,2,3. Since every potentially negative coefficient is represented in one of the classified cases, a verified replay plus the localization argument establishes the stated coefficientwise assertion for an arbitrary finite exterior set, not just the tested vertex counts.

Replay:

    PYTHONDONTWRITEBYTECODE=1 python3 universal_boundary_check.py

The finite certificate must be independently reconstructed and the localization argument audited before this candidate is promoted to an approved theorem. This is a computer-assisted proof route, not an ordinary unenumerated proof and not a proof-assistant certificate. Earlier floating-point searches are not used in this argument.

## Consequence if approved

Writing Gamma=1+(sum a_i)t+(sum b_ij)t^2+ct^3 for the exterior-only relation, the exact identity

    (sum b_ij)^2 - 3(sum a_i)c
      = 1/2 sum_(unordered distinct pairs e,f among {01,02,12}) (b_e-b_f)^2
        + 3 sum_i (b_ij b_ik-a_i c)

gives the last cubic Newton inequality by an explicit three-square identity plus coefficientwise nonnegative remainders. Actual degree three follows when c>0. A degree drop to at most two requires its corresponding actual-degree argument, rather than retaining cubic normalization.

The existing bipartite Lorentzian theorem already gives the scalar cubic inequality; the added content here is the coefficientwise boundary Rayleigh strengthening. Extending it through internal physical core arcs remains open. A naive assignment that splits every internal arc equally between its endpoint a_i and assigns each mixed degree-two support to its majority-role core pair fails; `internal_assignment_result.json` records a counterexample to that proposed intermediate inequality, not to ULC.
