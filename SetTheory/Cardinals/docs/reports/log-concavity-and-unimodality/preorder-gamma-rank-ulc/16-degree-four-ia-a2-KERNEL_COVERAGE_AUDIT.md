# Degree-four two-attachment kernel: complete independent audit

## Conclusion

The complete structural coverage and support-polynomial kernel in `enumerate.cpp` are approved. An independent full-domain reconstruction produces exactly the same 89,863 normalized polynomials, and individually verifies the core relation, marked attachments, direction mask, legal-type mask, and normalized polynomial of every stored representative.

The independently reproduced totals are:

- 40,877 weighted eight-vertex core cases
- 32,236 cores admitting at least one retained attachment specification
- 802,333 admitted core/attachment/direction specifications
- 667,508 specifications with a nonzero degree-four coefficient polynomial
- 89,863 distinct polynomials after exchanging the two singleton-type variables
- 89,863 stored representatives checked exactly

These are exhaustive combinatorial checks, not population samples. Positivity certificates for the resulting polynomials are a separate layer.

## 1. Why these templates cover the entire a=2 sector

At matching rank four, the canonical Gallai–Edmonds normal form with two attachments has a core K with |K|≤8 and ν(K−A)=2. The exterior vertices are independent singleton equivalence classes, every exterior neighbor lies in A, and each attachment has one direction toward all its exterior neighbors. Adding isolated vertices to the core preserves the polynomial and these conditions, so total core size eight suffices.

Every core preorder is covered by the quotient-poset generator and every positive block composition of eight. The complete proof of quotient coverage, collision-safe canonicalization, row-column twin suppression, and unrestricted class-size assignments is supplied in the accompanying finite/pendant audit. Its argument applies unchanged through quotient size eight. The independent reconstruction uses the same audited canonicalizer but constructs ideals and compositions separately, with compositions represented by separator subsets among seven gaps.

Every unordered pair A={a,b} is tried. Since K−A has exactly six vertices after padding, it has matching number greater than two exactly when it has a perfect matching. The production exclusion therefore retains precisely ν(K−A)≤2. This is a permissible enlargement of the canonical ν=2 domain. Any matching in a resulting expansion uses at most two edges touching A; all its other edges lie in K−A. Hence every retained expansion has matching number at most four.

For each pair, all four choices of the two attachment directions are tried. The nonempty exterior neighborhood types are exactly {a}, {b}, and {a,b}, numbered 1,2,3. There are no additional exterior equivalence classes or bidirectional attachment/exterior arcs in the canonical normal form.

For each type the implementation tests transitivity with two independent copies. This does not wrongly exclude a type occurring only once in a canonical preorder. A single valid exterior vertex has only unidirectional attachment arcs; cloning it cannot create a two-step path between its copies, because that would require opposite directions at the same attachment. Other transitivity conditions are already tested with one copy. Thus every type occurring in a canonical expansion passes the two-copy test.

All individually legal types are then tested together. Their simultaneous expansion is transitive. More generally, arbitrary multiplicities are valid: a failure of transitivity involves a path of length two and hence at most two exterior vertices. Distinct-type failures would already appear in the simultaneous one-copy test; equal-type failures would appear in the two-copy test. Equivalently, the fixed direction at each attachment directly excludes paths comparing two distinct exterior points.

A specification with no legal exterior type is omitted only because the finite core is already covered by the ten-vertex theorem. A specification whose degree-four coefficient polynomial is identically zero belongs entirely to the previously established degree-at-most-three theorem. Those omissions therefore leave no missing actual-degree-four case.

## 2. The support-level binomial kernel

Fix populations x₁,x₂,x₃ of the three legal types. In any directed matching support, each selected exterior vertex needs a different attachment. Therefore at most two exterior vertices occur. For a fixed set of selected exterior labels, feasibility depends only on their types and endpoint roles. It follows that each gamma coefficient has the exact expansion in the basis

1, x₁, x₂, x₃, binom(x₁,2), binom(x₂,2), binom(x₃,2), x₁x₂, x₁x₃, x₂x₃.

Each coefficient counts support pairs using exactly the specified selected exterior labels. In particular the coefficients are nonnegative integers, not numbers of matching witnesses.

### No selected exterior vertex

The coefficient is γ_k(K).

### One selected exterior vertex

For a leaf adjacent only to a, its partner is forced and the coefficient is γ_(k−1)(K−a). The same applies to b.

For a type-3 leaf, there are two possible partner choices. If the attachment directions differ, these choices place the leaf on opposite sides of the ordered support, so the support families are disjoint and their counts add.

If the directions agree, a support may admit both partner choices. It must contain both a and b on the partner side, and its opposite core side has one fewer element. The production `overlap` loop enumerates each such imbalanced ordered core pair exactly once and subtracts it if deleting a and deleting b both yield feasible balanced core supports. Thus it subtracts precisely the intersection of the two support families, once. Its two direction cases correctly reverse which side supplies the extra endpoint. The balanced feasibility table includes the empty support, so the lowest-degree endpoint cases are included.

The independent audit avoids this inclusion–exclusion implementation. For each imbalanced core pair it computes, using Hall inequalities, the set of attachment vertices whose deletion leaves a feasible residual support. It counts the pair once exactly when this set intersects the permitted leaf-partner neighborhood. This direct Boolean union yields the same complete one-leaf coefficients.

### Two selected exterior vertices

Both attachments are forced to be used, one for each selected exterior vertex. Removing these four endpoints leaves a support in K−A. The coefficient is therefore γ_(k−2)(K−A) times the number of distinct feasible endpoint-role patterns on the two selected exterior vertices and the two attachments.

The production `pairweight` routine tries the two attachment assignments and deduplicates the resulting leaf-role patterns. The attachment roles are determined by the fixed directions, so identical leaf-role patterns yield identical full four-vertex supports. This is exactly the required support count. The independent audit instead constructs this four-vertex directed graph and checks all balanced endpoint partitions with Hall’s criterion. It obtains the same factor for every type pair and direction choice.

For two vertices of the same type, choosing their labels contributes binom(x_t,2); for distinct types it contributes x_t x_u. This proves the entire kernel, including the binomial factors and every possible selected-exterior pattern.

## 3. Deduplication and representatives

Exchanging the attachment names exchanges x₁ and x₂ and leaves x₃ unchanged. In the stated binomial basis this permutes columns

1↔2, 4↔5, 8↔9,

with columns 0,3,6,7 fixed, using zero-based column numbers. Choosing the lexicographic minimum of a polynomial and this variable exchange is safe because the nonnegative integer population domain is invariant under the exchange. No assumption about a representative’s own symmetry is needed.

The output representative is not relabeled when its polynomial key is exchanged. This is intentional: the stored gamma array is the normalized key, not necessarily the literal polynomial in the representative’s original type order. The independent audit first recomputes the literal polynomial from the stored relation and marking, then applies the same final variable normalization. All 89,863 representatives match exactly. A consumer who needs literal type populations must account for this normalization rather than directly treating the stored array as unpermuted.

## 4. Independent full reconstruction

The independent `recount_a2.cpp` performs all of the following over the complete finite domain:

1. Regenerates quotient posets by maximal-element ideals and uses separator subsets for every positive block composition
2. Expands the weighted quotient into the eight-element preorder
3. Computes deletion matching numbers using a separate maximum-cardinality matching recurrence
4. Tests each candidate extension by independently taking its reflexive transitive closure and comparing it with the input relation
5. Computes every balanced core support with Hall’s criterion, using disjoint ternary vertex roles
6. Computes all one-leaf coefficients by direct support unions and all two-leaf role factors by four-vertex Hall tests
7. Rebuilds the entire normalized polynomial set and compares it with the output set
8. Checks the legal-type mask and normalized polynomial of every stored representative individually

All asserted counts and both set/representative comparisons pass. The full output is in `recount_a2.log`.

The only reused computational component is the exact canonicalizer, whose coverage and invariance have been proved directly. Known poset counts, witness examples, and small population grids are not being substituted for the coverage proof.

## 5. Using this audit with a positivity certificate

To conclude rank-ULC in the full a=2 sector, certify the second and third order-four gaps for these 89,863 polynomial families on every nonnegative integer population triple. The universal first Newton inequality already supplies the first gap. At population values where the actual degree drops below four, use the established lower-degree theorem and its actual-degree normalization.

A decomposition into faces x_i=0 or x_i=1+y_i, y_i≥0, is sufficient for the integer domain: each nonnegative integer coordinate is either zero or at least one. Such a face certificate should not be described as positivity on the entire real nonnegative population orthant unless values between zero and one are separately treated. This distinction does not affect the preorder theorem, whose populations are integers.
