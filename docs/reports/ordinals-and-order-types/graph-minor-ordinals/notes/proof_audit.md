# Proof audit and dependency map

Date: 20 September 2026.

## External theorems actually used

1. The de Jongh--Parikh maximal-linearization theorem, and natural-sum/product
   formulas for disjoint sums and Cartesian products of well-partial-orders.
2. Well-quasi-order closure under finite multisets (obtainable from Higman's
   theorem).
3. The finite-multiset embedding maximal-order-type formula **only below
   epsilon_0**: o(M_emb(P)) = omega^o(P). The unrestricted theorem has a correction
   in its exponent; the manuscript does not drop that correction above its range.
4. The Kriz--Thomas height--width inequality: w(P) <= o(P) <= h(P) natural-product w(P).

The finite-cover width bound, finite-grid widths, and the transferable-product
lower bound are proved in the manuscript. No lexicographic-product formula from
an older survey is used.

## Connected-component transfer

- A target connected component belongs wholly to one source connected component
  in any minor model.
- Several target components may come from one source component. Ignoring this
  possibility would compute a different relation.
- If one target component is isomorphic to its source component C, its branch
  sets use all |V(C)| vertices, leaving none for another target component.
- Otherwise every retained target component is a proper connected minor of C.
  Its exponent is strictly lower in any connected linearization.
- A finite natural sum of lower-exponent monomials is strictly below the original
  monomial. Natural sums preserve this decrease when other components are added.
- Every Cantor-normal-form polynomial below omega^alpha is represented by a
  unique disjoint union when the connected linearization is bijective onto alpha.
- Multiset matching supplies an upper bound, not an asserted isomorphism of the
  graph-minor relation with multiset embedding.

## Degree-two geometry

- P_n has n vertices, not n edges. C_n is a simple cycle and n >= 3.
- A cycle that remains cyclic consumes its entire source cycle. Shortening a
  retained cycle by contraction does not release vertices for a separate path.
- A path or an unused cycle of n vertices can supply a linear forest precisely
  when the sum of target path vertex counts is at most n. Cutting consecutive
  segments needs no extra separating vertex.
- Cycle reservation has a valid smallest-fitting-source greedy exchange proof.
  General path bin packing does not thereby become greedy.
- In the exact-k-cycle layer every source cycle is reserved. This is why the
  path/cycle factorization is an actual Cartesian product on that layer, even
  though it is only a weaker comparison on the at-most-k-cycle class.
- Simple-graph contraction sends C_3 to P_2, not to an inadmissible two-cycle.

## Ordinal arguments

- The connected path/cycle order has maximal order type omega*2, not omega.
- The full degree-two code is maximal on the unrestricted class, but generally
  is not maximal on finite-cycle-budget subclasses. Its restriction has type
  omega^(omega+1) for every positive finite budget; budgets >= 2 have larger
  actual maximal order types.
- The intrinsic rank of a single unrestricted degree-two graph is |V|+|E|, a
  finite integer. Its position in a maximal linearization is a different rank.
- omega^(omega*2) is **not** assumed multiplicatively indecomposable. The proof
  directly checks omega natural-product beta < omega^(omega*2) for every smaller
  beta, using the possible Cantor-normal-form exponents.
- The finite-cycle-budget width proof uses a transferable-product lower bound,
  not an unjustified inversion of the height--width inequality.
- Removing finitely many principal lower sets from the linear-forest order
  removes finitely many elements. Additive indecomposability of its width makes
  this width-preserving.
- Transfinite induction in the product lemma uses ordinary multiplication in
  the specified order and continuity in the right argument.
- Increasing-union lower bounds use monotonicity only. The noncontinuity examples
  compute both sides independently; they never exchange union and tree rank.

## Computational evidence

The saved report verifies all ordered pairs on all 1,500 degree-two isomorphism
classes with at most fourteen vertices. Elementary-operation closure and packing
are independently specified descriptions of the relation. The greedy and
exhaustive cycle-reservation implementations share an exact path-packing solver.
Generating-function coefficient counts independently check the enumeration.

This evidence tests graph-theoretic lemmas and implementations over a stated
finite range. It is not a computer verification of a transfinite theorem or a
priority search. The manuscript is neither externally refereed nor formalized.
