# Proof dependencies

This file maps the merged article. Section numbers refer to
`friendly_order_types.tex`.

## Imported background

- de Jongh--Parikh (1977): maximal well-order linearizations exist for wpos;
  maximal order type of a Cartesian product is the natural product.
- Vialard (MFCS 2023), Corollary 4.7: if o(P) is a nonzero limit and
  o(str(P)) = o(P), then f(P) = o(P).
- Vialard (MFCS 2023), Theorem 3.4, equivalently thesis Definition 5.3.2 and
  Theorem 5.3.3: w(M^r(P)) = omega^(f(P)). Used only for multiset
  consequences, never to prove the finite or mixed-product formula.
- Vialard (MFCS 2023), Definition 3.3: the invariant o_perp itself.
- Vialard (MFCS 2023), Proposition 4.1(1): the binary ordinal-sum law, which
  is known; a self-contained residual proof is given anyway, to fix the
  direction of ordinal addition and to support the transfinite extension.
- Dzamonja--Schmitz--Schnoebelen (2020): standard rank conventions for
  ordinal invariants of wqos.

## Finite theorem (Theorem 3.6, f(P) = |P| - c(P))

This is the shared core theorem of the two merged reports, and both proved
it by the same argument. It is proved once here.

Uniform orientation between incomparability components
  -> components are linearly ordered blocks (Lemma 3.1)
  -> the canonical ordinal-sum decomposition P = C_1 + ... + C_c.

A friend lies in the same component as its choice
  -> at most |C|-1 selections per component (Lemma 3.2, capacity)
  -> upper bound |P| - c(P) (Corollary 3.3).

Finite connected incomparability graph, with any prescribed minimal root r
  -> a maximal non-cut vertex distinct from r exists (Lemma 3.4)
  -> a legal deletion sequence of length |C|-1 leaving exactly r
     (Proposition 3.5, connected case).

Descending processing of the components
  -> matching lower bound.

No imported transfinite theorem is required in this branch. The
protected-root clauses of Lemma 3.4 are the strengthening carried over from
the second report; Theorem 4.1 depends on them.

## Maximum subsets and certificates (Section 4)

Protected-root construction (Proposition 3.5) + capacity (Lemma 3.2)
  -> the maximum friendly subsets are exactly the complements of one
     minimal element per component (Theorem 4.1), counted by the product of
     |Min(C_i)|.

Orienting each witness edge from choice to friend, strictly increasing
deletion time
  -> acyclicity and spanning (Proposition 4.2)
  -> f(P) is the graphic-matroid rank of Inc(P), so f(P^op) = f(P)
     (Corollary 4.3).

This reading is finite only; Proposition 10.6 shows it fails on infinite
wpos.

## Product component theorem (Theorem 5.2)

Projection comparison across an ordinal cut L+U in A x B
  -> at least one side of the cut is a singleton (Lemma 5.1)
  -> exactly one non-singleton incomparability component
  -> other components are precisely existing endpoints.

This branch works for arbitrary posets, not only wpos or finite posets, and
it is the branch reused by the transfinite argument.

## Finite product formula: TWO PROOFS, both retained

1. Projection route (Section 5.1-5.2): Lemma 5.1 + Theorem 5.2 + the finite
   theorem. This is the main line, because Lemma 5.1 needs no finiteness and
   is used again in Section 8.
2. Chain-grid route (Section 5.3, Theorem 5.4): pick linear extensions; the
   incomparability graph of the chain grid is a spanning subgraph of
   Inc(A x B); the incomparable anchors (0,n-1) and (m-1,0) connect every
   non-corner vertex; the two corners are then classified directly. This
   proof is finite-only but entirely self-contained: it imports neither the
   cut lemma nor any projection argument.

Neither proof is dropped. What the second buys is stated in the article: a
reader wanting only the finite product formula can avoid the import.

## Substitution (Theorem 5.6)

Fibers over different base components are completely comparable
  -> no cross edges;
adjacent fibers are completely incomparable
  -> paths lift, so the fibers over one non-singleton base component form a
     single incomparability component of size sum |Q_p|.
Singleton base components contribute f(Q_p) unchanged.
Empty fibers are excluded and require deleting their base vertices first.

## Counterexample (Theorem 6.2)

Finite theorem + product component theorem
  -> D = 1 + antichain_2 + 1 and E = antichain_2 + 1 + 1
  -> both have invariants (4,3,2,1)
  -> multiplication by the same chain_2 gives friendly types 5 and 6.

Explicit antichains and chain covers also show that both product triples
(o,h,w) equal (8,4,3).

Two separate, weaker statements sit beside it and are distinguished in the
text: Example 6.1 (three elements already defeat (|P|,o,h,w)) and
Proposition 6.3 (the gap can be n-2, which is maximal). Neither is a
counterexample to Question 1.2, because those posets differ in f itself.

## Mixed-product theorem (Theorem 8.1)

Natural-product calculation
  -> if some ordinal factor is limit, total maximal type is limit
  -> product component theorem + absorption of a least point
  -> imported limit saturation.

When all ordinal factors are successors:

1. Write alpha_i = lambda_i + m_i with lambda_i nonzero limit, m_i positive
   finite. Let T be the full finite upper corner of size N; let Q=P\T.
2. An attained maximal linearization, finite deletion from a limit ordinal,
   and the upper-set property show o(Q)=Lambda when o(P)=Lambda+N.
3. An incomparable friend in T can be moved to Q by replacing a deficient
   coordinate with x_i+1 < lambda_i. Thus stripping Q removes at most its
   least point.
4. Imported limit saturation gives f(Q)=Lambda.
5. If B has no greatest element, every point of T has a permanent friend
   in Q. Reverse-linear-extension deletion selects all N points.
6. If B has a greatest element, stripping P yields the upper bound
   Lambda+(N-1). Top-edge deletion followed by reverse-linear-extension
   deletion of the remaining corner achieves N-1 selections, with explicit
   surviving friends. For N=1, subposet monotonicity suffices without a move.
7. The residual rank equation adds these finite successors on the right.

This proves the theorem for arbitrary infinite ordinal factors, without
countability or a below-epsilon_0 assumption.

## Ordinal boxes (Theorem 9.1)

Remove zero and singleton degeneracies. Finite factors give the finite
endpoint formula; in the infinite case collect finite factors into B and
apply the mixed theorem.

## Ordinal sums and transfinite values (Section 10)

The binary formula is known and reproved by induction on f(B); the induction
may equally be run on the rank of Bad(B), which is a choice of measure, not a
different proof. At a limit index, a first move removes every higher block,
giving the supremum of initial-sum ranks. This is ordinary, not natural,
ordinal addition.

Sum law + finite theorem
  -> finite-block formula, and the evaluation of any wpo all of whose
     incomparability components are finite (Corollary 10.4);
  -> every ordinal alpha is realized by a sum of alpha two-element
     antichains, at ordinary antichain width two (Corollary 10.5);
  -> for countably infinite alpha these posets have isomorphic
     incomparability graphs, so on infinite wpos f is not a function of the
     graph (Proposition 10.6).

Proposition 10.6 is a mathematical obstruction and must not be confused with
the separate methodological caution in Section 9.3, that numerical suprema of
finite grids do not compute a transfinite rank. The article distinguishes
them explicitly.

## Enumeration (Theorem 11.1)

In a natural labelling the components occupy consecutive label intervals
  -> the decomposition is a unique ordered list of connected pieces
  -> A(z) = 1/(1-B(z)), and weighting a size-m piece by z^m u^(m-1) gives the
     bivariate distribution; a_{n,k} = [z^n] B(z)^(n-k).
  -> fixed-rank counting polynomials of degree k with leading coefficient
     1/k! (Corollary 11.2).

The numerical values a_n and b_n are outputs of the included enumeration.

## Verification layer

Two independent finite engines are used. `code/friendly.py` carries the
protected-root construction, the certificate verifier, substitution and
duals, and drives the exhaustive size-seven run. `code/finite_posets.py` is a
separate representation with its own enumerator, residual DP and
search-based certificate routine, and supplies heights, widths and products
for the counterexample. The residual DP checks the component formula
independently of the formula and of the non-cut lemma. The constructive
strategies check the existence part. Corner simulations check finite witness
logic only. Symbolic CNF tests check arithmetic identities and evaluation of
stated formulas only. The generating-function script is a consistency check
on saved counts. None is a formal proof assistant verification of anything,
and none verifies a transfinite theorem.
