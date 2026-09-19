# Proof dependencies

## Imported background

- de Jongh--Parikh (1977): maximal well-order linearizations exist for wpos;
  maximal order type of a Cartesian product is the natural product.
- Vialard (MFCS 2023), Corollary 4.7: if o(P) is a nonzero limit and
  o(str(P)) = o(P), then f(P) = o(P).
- Vialard (MFCS 2023), Theorem 3.4: w(M^r(P)) = omega^(f(P)). Used only for
  multiset consequences, never to prove the finite or mixed-product formula.

## Finite theorem (Theorem 3.4)

Uniform orientation between incomparability components
  -> components are linearly ordered blocks.

Finite connected incomparability graph
  -> a maximal non-cut vertex exists
  -> a legal deletion sequence of length |component|-1 exists.

One never-selected witness in each original component
  -> upper bound |P|-c(P).

Descending processing of the components
  -> matching lower bound.

No imported transfinite theorem is required in this branch.

## Product component theorem (Theorem 4.2)

Projection comparison across an ordinal cut L+U in A x B
  -> at least one side of the cut is a singleton
  -> exactly one non-singleton incomparability component
  -> other components are precisely existing endpoints.

This branch works for arbitrary posets, not only wpos or finite posets.

## Counterexample (Theorem 5.1)

Finite theorem + product component theorem
  -> D = 1 + antichain_2 + 1 and E = antichain_2 + 1 + 1
  -> both have invariants (4,3,2,1)
  -> multiplication by the same chain_2 gives friendly types 5 and 6.

Explicit antichains and chain covers also show that both product triples
(o,h,w) equal (8,4,3).

## Mixed-product theorem (Theorem 7.1)

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

## Ordinal boxes (Theorem 8.1)

Remove zero and singleton degeneracies. Finite factors give the finite
endpoint formula; in the infinite case collect finite factors into B and
apply the mixed theorem.

## Ordinal sums (Theorem 9.2)

The binary formula is known and reproved by induction on f(B). At a limit
index, a first move removes every higher block, giving the supremum of
initial-sum ranks. This is ordinary, not natural, ordinal addition.

## Verification layer

The finite residual DP checks the component formula independently. The
constructive strategy checks the existence part. Corner simulations check
finite witness logic only. Symbolic CNF tests check arithmetic identities
and evaluation of stated formulas only. None is a formal proof assistant
verification of the transfinite theorem.
