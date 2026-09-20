# Proof audit and dependency map

## Status

The supplied manuscript is an unrefereed, AI-assisted research attempt. Its
claims have English proofs and finite computational checks. No proof-assistant
formalization, independent referee report, or verified priority claim is supplied.

## What is classical

Jacobsthal multiplication is transfinite iteration of natural addition.
Its binary CNF formula and its associativity are classical. Ordinary finite-support
colex products are standard. The natural product is the largest order type of a
linear extension of a finite componentwise Cartesian product (Carruth).

The article reproves the binary CNF formula to state its exact dependencies.
The new construction is presented for evaluation, not the classical numerical
identities in isolation.

## Dependency graph

1. Ordinary CNF arithmetic gives absorption by a positive pure omega power.
2. Absorption and natural finite multiples identify the binary Jacobsthal formula
   directly from the defining recursion.
3. Canonical input blocks give a finite pivot partition of the Cartesian set.
4. Each cell receives ordinary colex and has a pure monomial order type.
5. Distinct pivot layers are strictly separated in exponent; within one layer,
   exponent comparison is exactly input block-exponent comparison.
6. Thus the primitive pivot order sorts the monomial cell types without needing
   to calculate prefix ordinal sums in its comparison rule.
7. The cell formula identifies the binary operation and supplies degree and tail
   metadata for all finite arities.
8. Finite regrouping follows by comparing the multisets of unit monomial blocks.
   Jacobsthal associativity is a conclusion, not a premise of this proof.
9. Separately, the binary formula preserves common CNF support, common leading
   monomial, and coefficient domination for ordinary/Jacobsthal partial products.
10. The same-leading-monomial estimate gives O <= J < O*2.
11. At a cofinally active limit, a later ordinary factor >=2 overtakes each earlier
    Jacobsthal value. The limit values are equal.
12. Repeated later growth makes the common limit additively indecomposable and
    hence a pure omega power.
13. Erasing units and isolating the finite active suffix gives the product reduction.
14. Ordinary finite-support colex on the prefix and the finite pivot order on the
    suffix supply the direct arbitrary-arity comparison rule.
15. The equality automaton follows from the exact coefficient update rules.

## Delicate points checked in the text

### Prefix addition is ordinary, not natural

The type of a cell with pivot j and block exponent sigma is
omega^(D_(j-1)+sigma), where D is an ordinary sum of leading exponents.
Finite integer exponent tests alone would not test the distinction, so the
additional test pool includes nested transfinite exponents.

### There are no collisions across different pivot layers

A pivot-j exponent is at most D_j. A later pivot-k exponent, k>j, is strictly
larger than D_(k-1), which is at least D_j. Therefore different pivot layers
cannot have equal exponents. Ordinary absorption of a prefix does not defeat
this argument. Within one pivot, addition of its fixed prefix degree is strictly
increasing in the block exponent. Equal exponents can still occur from repeated
unit blocks and multiple finite-tail choices; their tie rule must be specified.

### Coordinatewise comparisons cannot move the pivot right

Once a coordinate lies in its final finite interval, increasing it leaves it
in that interval. Thus a componentwise increase can only move the last
positive-block coordinate left. The pivot ordering then compares the tuple in
the correct direction. Equal pivots are handled by block and tail comparisons.

### Regrouping does not mean flattening is order-preserving

For factors (omega+1, 2, omega), the direct order places (omega,0,0) before
(0,1,0), whereas flattening the nested order F(F(omega+1,2),omega) reverses
that comparison. The proof uses order isomorphisms of matched monomial blocks,
not the flattening identity. Unique order isomorphisms ensure finite coherence.

### The cofinal limit argument stays below its endpoint

Given xi<lambda and a later active factor at i<lambda, one has i+1<lambda
because lambda is a limit. Thus J_xi < O_xi*2 <= O_(i+1) really compares with
an earlier partial value, and taking suprema proves equality. No continuity
in the left argument of Jacobsthal multiplication is assumed.

### The active index matters more than the ambient index

The sequence (omega+1,2,1,1,...) has ambient length omega but active length 2.
Its ordinary and Jacobsthal products differ. Unit erasure is a theorem, and
only afterward is the unique decomposition tau=lambda+n used.

### Zero is handled outside the nondecreasing recursion

The main limit proofs require all factors nonzero. A zero factor makes the
finite-support set empty and the product zero. Taking the supremum of the
entire history after a drop to zero would be wrong; the article explicitly
uses the absorbing-zero extension instead.

## Extremal characterization

For finite factors, restrict to componentwise linear extensions whose induced
orders on the specified pivot cells are ordinary colex. A rank-vector argument
bounds every such extension by the natural sum of the cell types. Sorting the
pure monomials attains the bound. The same argument works with a pure-power
infinite prefix attached to the finitely many suffix cells.

This is restricted maximality. It is not maximality among every linear
extension of the unrestricted infinite finite-support product; that partial
order can contain an infinite antichain.

## What the computer checked

The driver compares the all-arity formula with binary iteration and every
finite split for each tested list. It checks support, leading monomial,
coefficient domination, the factor-two bound, degree/tail metadata, the natural
upper bound, and the three-state classification. Separate sampled-point tests
compare the primitive and degree-based ordering rules and check componentwise
extension and elementary comparator laws.

All exact test expressions are below epsilon_0. The arithmetic kernel is shared
between several test paths. Limits are not evaluated by the test program. The
mathematical proofs, rather than the tests, carry the arbitrary-ordinal claims.

## Not settled or not claimed

No CNF-free universal characterization, preservation by arbitrary embeddings,
explicit pointwise formula for every transfinite regrouping isomorphism,
independent resolution of all of Altman's Question 5.2, super-Jacobsthal
exponentiation model, or exhaustive novelty certification is claimed.
