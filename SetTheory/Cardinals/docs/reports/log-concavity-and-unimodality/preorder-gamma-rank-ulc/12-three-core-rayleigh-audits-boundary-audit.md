# Independent audit of the three-core coefficientwise boundary inequality

Date: October 1, 2026. Verdict: **APPROVED as a computer-assisted all-size theorem**.

The localization argument and complete finite enumeration prove, for a directed
relation on a physical bipartition `C∪I`, `C={i,j,k}`, with arbitrary directions
and opposite arcs,

    b_ij b_ik − a_i c ≥_coeff 0

in the original independent tail/head activity variables. The support
polynomials `a_i,b_ij,c` have exactly the definitions in the producer's
`COEFFICIENTWISE_BOUNDARY_LEMMA.md`. No internal physical core arcs are allowed.

This conclusion is computer-assisted: the mathematical reduction is unbounded,
while a complete finite family of exact integer calculations supplies the last
step. It is not inferred from random searches, and no proof-assistant
formalization or ordinary nonenumerative proof is claimed.

## 1. All-size localization is complete

Fix the distinct core labels as `i=0,j=1,k=2`. In a product contributing to
`b_01 b_02` or `a_0 c`, physical core vertex 0 occurs twice and vertices 1 and 2
occur once each. The exterior physical multiplicities sum to four. Each factor
is squarefree in physical vertex use, although a vertex may recur in both
factors and its two roles may then agree or differ.

A negative gap coefficient must have a nonzero coefficient in `a_0 c`.
The first factor uses one exterior vertex and the second uses three distinct
exterior vertices. The possible exterior unions are therefore exactly:

- Four distinct vertices with multiplicities `1,1,1,1`
- Three distinct vertices with multiplicities `2,1,1`

Other monomials have zero negative contribution and need no test. This includes
the two-distinct-vertex pattern `2,2`, which may occur in the positive product.
Exterior sets of size below three cause no difficulty because `c=0`.

For a fixed formal monomial, every factor contributing to its coefficient uses
only vertices whose role variables occur in that monomial. A directed perfect
matching between its chosen endpoint sets cannot use another vertex as an
intermediate point. Consequently deletion of all other exterior vertices
preserves both product coefficients exactly, rather than merely bounding one
of them. Deleting an arc whose tail or head role variable is absent likewise
preserves the coefficients. These observations justify restricting to the
compatible directed arc bits on the selected three or four exterior vertices.

Exterior relabeling also relabels the independent variables and preserves the
coefficient counts. Thus it legitimately reduces the four-vertex role patterns
to one canonical ordering for each number of exterior tails. It does not
identify activities or insert multiplicity factors.

## 2. Role exponents and finite coverage

Every product has total tail degree four and total head degree four. Let the
tail exponent at doubled core 0 be `c_0∈{0,1,2}`, and the tail exponents at
single-use core vertices 1 and 2 be `c_1,c_2∈{0,1}`. The complementary head
exponents are `2−c_0,1−c_1,1−c_2`.

For four distinct exterior vertices, their required number of tail roles is
`4−c_0−c_1−c_2`, always between zero and four. Canonically place those tails
first. This gives 12 types, comprising 11,392 compatible directed subgraphs.

For three exterior vertices, label the doubled vertex first and write its tail
exponent as `e_0∈{0,1,2}` and the other two as `e_1,e_2∈{0,1}`. Retain exactly

    c_0+c_1+c_2+e_0+e_1+e_2=4.

There are 36 tuples. As an independent counting check, 36 is the coefficient
of `x^4` in `(1+x+x²)²(1+x)^4`. They comprise 5,984 compatible directed
subgraphs. Including both families gives exactly 48 types and 17,376 graphs.

An arc `a→b` is included among the possible bits exactly when the tail
exponent at `a` and the head exponent at `b` are both positive. Both directions
of a physical edge are independent bits when both qualify. All subsets of
these bits are checked. No role-exponent or physical-overlap case is omitted.

## 3. Ordered factors and counting multiplicities

At a doubled vertex, two identical roles have just one allocation to the two
ordered factors; mixed roles have two allocations. There is no binomial
coefficient beyond those genuine choices. The factors are distinguished by
their core sets, so exchanging the factors is not a symmetry by which to
divide.

In the four-exterior case, choosing the two exterior vertices for `b_01` gives
six positive allocations; choosing the exterior singleton for `a_0` gives four
negative allocations. In the three-exterior case the doubled exterior belongs
to both positive factors and to both negative factors. There are two ways to
assign the singleton exterior vertices to the positive factors and one way to
assign the negative singleton's physical vertex. Role allocations at the two
doubled vertices then determine the full ordered support pair uniquely.

The producer tests existence of a compatible bijection by a Boolean predicate.
Several matching witnesses for the same endpoint support do not increase its
coefficient. The audit found no factorial, matching-witness, or repeated-role
overcount in this routine.

## 4. Independent reconstruction

The independent program `independent_boundary_check.py` imports no producer
code and uses a different counting route. For every reduced graph it starts
with the empty matching support, adjoins arcs only when their physical
endpoints are unused, and deduplicates the resulting ordered endpoint masks.
This enumerates every feasible directed support exactly once as a set element.

It represents each support's formal monomial by a base-three integer with one
digit for each of the `2|V|` independent role variables. Each individual support
has digits zero or one; the product of two supports has digits at most two,
so addition of these integers has no carries. Integer equality therefore tests
exact equality of the original formal monomials, including `u_v²`, `u_v v_v`,
and `v_v²` distinctions. Coefficients are obtained by exact complement lookup
between the appropriate support families, not by reproducing the producer's
role-allocation/permutation formula.

Results:

- All 48 types and 17,376 graph cases passed
- 228,264 support instances were enumerated
- The fixed target coefficients range from zero through three
- Every one of the 48 per-case coefficient histograms exactly matches the
  producer's independent receipt

The complete independent histograms are in `independent_receipt.json`. The
producer's receipt and code were compared by content and are identified in
`approval_receipt.json`.

The localization proof plus this complete finite verification establishes the
claim for every finite exterior size. Core relabeling proves all three choices
of the repeated core vertex. Nonnegative activity evaluations, including zero
activities, follow immediately from coefficientwise nonnegativity; no limiting
argument is necessary.

## 5. Consequences and limits

For the core-monomer polynomial

    f=z_0z_1z_2+Σ_i a_i z_jz_k+Σ_(i<j)b_ij z_k+c,

the proved expression is exactly the Rayleigh difference in `z_j,z_k` evaluated
at all three core monomers equal to zero. It does not by itself establish real
stability, all Rayleigh differences at arbitrary real monomer values, or a
coefficientwise inequality with internal core arcs restored.

The proposed scalar consequence is algebraically correct:

    (Σ b_e)²−3(Σ a_i)c
      = 1/2 Σ_(unordered distinct e,f)(b_e−b_f)²
        +3Σ_i(b_ij b_ik−a_i c),

where `e,f` range over `01,02,12`. This yields the last degree-three Newton
inequality on nonnegative activity evaluations. The squared differences need
not be coefficientwise nonnegative; thus the identity is a scalar
sum-of-squares consequence, not a claimed coefficientwise Newton certificate.
If `c=0`, actual-degree normalization still requires its own argument.

The exploratory counterexample to a proposed internal-core assignment is not
a counterexample to this theorem, whose bipartite physical hypothesis excludes
those arcs. It is also not being described as a counterexample to ULC.

The previous released structural paper and archive were not modified.
