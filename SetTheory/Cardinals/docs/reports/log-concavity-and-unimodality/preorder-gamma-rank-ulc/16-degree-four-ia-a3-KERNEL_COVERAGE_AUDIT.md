# Degree-four three-attachment kernel and coverage: independent audit

## Verdict

The complete three-attachment structural coverage, component pruning, marked-template canonicalization, binomial-basis support kernel, and gamma-polynomial aliases are approved. Positivity of the resulting Newton gaps is a separate certificate layer and is not asserted by this note.

A fully independent reconstruction, importing no producer code or canonicalizer, reproduces all counts and the complete marked-template set. Hall's condition independently recounts every coefficient of every stored representative:

- 854 weighted six-vertex cores
- 90,042 legal core/attachment/orientation specifications
- 68,704 structurally reduced specifications
- 21,338 retained specifications
- 6,213 canonical marked templates
- 188,715 selected-exterior quota vectors and 943,575 scalar coefficients
- 3,437 distinct gamma arrays, with all aliases and representative metadata verified

The audit was compiled with undefined-behavior sanitization and completed without an assertion, mismatch, or sanitizer finding. See `recount.log`, `preparation.json`, and `kernel_audit.json`.

## 1. Structural domain and exhaustive core coverage

Use the already established Gallai--Edmonds bounded-core normal form for actual matching rank four. With three attachments A, the core K has at most 3·4−2·3=6 vertices and the exterior is an independent set of singleton classes with neighbors only in A. Its deletion matching number is one. Padding K by isolated vertices reaches six without altering the support polynomial; K−A then has three vertices, so the weaker requirement ν(K−A)≤1 is automatic for every enumerated core.

Each attachment has one strict direction toward all its exterior neighbors. Opposite directions toward two exterior vertices would force those vertices comparable by transitivity. Equivalence across A and the exterior is impossible: equivalent elements are twins in the comparability graph, so swapping them is an automorphism preserving the canonical Gallai--Edmonds D set, whereas an exterior singleton lies in D and an attachment does not. Zero-neighborhood exterior vertices are isolated and never occur in a matching support; they can be discarded.

Every preorder is a strict quotient poset with positive equivalence-block sizes. The independent audit enumerates all upper-triangular relations on m≤6 vertices, retaining exactly the transitive ones. A linear extension of every finite poset supplies such a labeling. It then tries every one of the m! vertex permutations and deduplicates by the entire adjacency matrix. Thus its canonicalization is exact and cannot merge nonisomorphic quotient posets. This is independent of the producer's maximal-element extension and color-refinement canonicalizer.

Natural-label counts are 1,2,7,40,357,4824; the independently obtained unlabeled counts are 1,2,5,16,63,318. All positive block compositions of six are reconstructed from separator subsets of the five gaps. This gives Σ p_m binom(5,m−1)=854 weighted cores. Every unordered attachment triple and all eight direction masks are tested.

## 2. Legal types and arbitrary populations

The seven nonempty types are exactly the subsets of the three attachments. For each type, the independent audit compares the reflexive transitive closure of its one-copy and two-copy extensions with the supplied relation. Both tests agree for every enumerated specification. Every union of individually legal types also passes transitivity.

These finite tests are complete for arbitrary multiplicities, not population sampling. A transitivity failure involves a two-edge path and at most two exterior vertices. Equal-type failures are detected with two copies; unequal-type failures are detected in the simultaneous one-copy extension. More directly, the fixed direction at an attachment prevents any two-edge path from one exterior vertex to another. Duplicating an individually valid exterior vertex therefore introduces no new comparison requirement.

Specifications having no legal type reduce to a core of size at most six, covered by the previously established finite/lower-degree results.

## 3. Component pruning is valid for every population

Take one clone of every legal type. Positive repetitions do not change connectivity, the partition into components, or bipartiteness. For a component H, let A_H be its active attachments, namely the attachments adjacent to at least one exterior type in H. Put K_H=K∩H.

The maximum possible matching number of this component over all populations is exactly

|A_H| + ν(K_H−A_H).

For the upper bound, a matching has at most |A_H| edges touching active attachments; after their removal all remaining nonisolated vertices lie in K_H−A_H. For attainment, use three clones of each present type. Assign each active attachment to a clone of an incident type; three copies suffice because there are at most three active attachments. Choose different copies whenever assignments use the same type. These clone edges are disjoint and can be combined with a maximum matching of K_H−A_H.

Thus the producer's formula is a proved maximum-population rank, not an inference from testing population three. It is always at most four: for a=|A_H|≤3, the residual core has at most 6−a vertices, and a+floor((6−a)/2)≤4.

If every one-copy component is bipartite or has this maximum rank at most three, the entire specification is safely omitted. At zero populations components may split, but deleting clone vertices cannot increase matching number or destroy bipartiteness, so the same reduction applies to every face.

A bipartite comparability component is a legitimate bipartite support problem. In a connected component with at least three vertices, an equivalence edge would force a triangle, and a directed path through three distinct vertices would also force a triangle. Hence all arcs are strict, every vertex is a source or a sink, and the two sets are disjoint shores. Its ordered disjoint supports are exactly the ordinary matchable shore-subset pairs, counted once. The established bipartite matching-rank-at-most-four ULC theorem therefore applies at unit activities. A bidirectional two-vertex component separately has polynomial 1+2z. Nonbipartite components of rank at most three use the established preorder theorem. Supports split uniquely over components, so their polynomials multiply; finite-order ULC convolution proves the componentwise reduction.

## 4. Canonical marked templates

The producer tries all 3! permutations of attachments, all 3! permutations of the remaining core vertices, and global reversal of every arc. The complete key consists of six adjacency rows, the three-bit direction mask, and the seven-type legality mask. Type labels and direction bits are transformed with the attachment permutation; reversal transposes the relation and flips every direction bit.

Every equality of keys explicitly exhibits a permissible isomorphism or global duality. Global duality preserves gamma by exchanging the two endpoint sets. No other variable or sign identification is made. The independent audit reconstructs this orbit minimum itself, checks that every stored representative is minimal, and compares the entire regenerated set with the 6,213 stored keys.

## 5. Exact binomial support kernel

Let M_t denote the population of each legal type. Every selected exterior vertex in a feasible support needs a distinct partner among the three attachments, so at most three exterior vertices can be selected. For each quota vector q with total at most three, choose q_t fixed labeled vertices of type t and require that all those vertices occur in the ordered support. Let c_(k,q) count the resulting feasible disjoint k-element endpoint pairs. Then exactly

γ_k(M) = Σ_(|q|≤3) c_(k,q) ∏_t binom(M_t,q_t).

The choices of selected exterior labels contribute precisely the displayed binomial factors. Clone permutations preserve feasibility, while unselected vertices cannot participate in a matching witnessing a fixed support. Therefore this is an exact identity for every nonnegative integer population, with no bounded-population extrapolation.

The producer loops over disjoint tail/head masks of equal size at most four, requires every selected exterior label to appear, and tests directed perfect-matching existence as a Boolean. It counts each support once even if several matchings exist.

The independent audit instead assigns each core vertex one of three roles (absent, tail, head), each mandatory exterior vertex one of two roles, and filters for equally sized endpoint sets. It checks every nonempty subset S of the tail set using Hall's condition |N(S)∩heads|≥|S|. Candidate counts for 0,1,2,3 mandatory exterior vertices are respectively 141,252,462,856. Every one of the 943,575 stored scalar coefficients agrees. No producer matching recurrence is reused.

The independent parser also verifies the complete quota domain, all array dimensions, nonnegative integer entries, consecutive IDs, and type ordering. Counts beyond degree four are impossible by the structural matching bound, and coefficients of population degree beyond three are impossible by the distinct-attachment argument.

## 6. Gamma aliases and reproducibility

Distinct gamma arrays are identified only when both the ordered quota array and all five coefficient arrays agree literally. Variables are generic population coordinates in their stored order, so equality certifies identical polynomials even when template neighborhood names differ. The independent parser verifies all 6,213 alias entries, all 3,437 unique representatives, and their original template IDs and metadata.

Run `python3 prepare.py`, compile `recount.cpp` with C++17, and run the resulting executable on `representatives.txt`. Assertions must remain enabled. The check uses only the standard libraries; it imports neither production code nor a third-party algebra library. The source and certificate hashes are recorded in the receipts.

This audit establishes coverage and kernel correctness. It does not itself certify the second and third Newton gaps on every population face; that independent algebraic verification is the remaining layer.
