# Proof audit

## Central claims

A. For every Noetherian X, the extended lower-Vietoris Hoare powerspace
   has stature at most the ordinal `2^(||X||)`.
B. This is attained at every ordinal, even by T1 spaces.
C. At `omega+n`, every value is exactly
   `omega*j(U) + (j(Q)-j(U))`, and every finite pair `(Q,U)` is realized.

The source TeX gives complete English arguments for these assertions.
There is no machine-checked transfinite formalization in this package.

## Dependency structure

Elementary well-founded ranks
  -> rank monotonicity; no gaps; finite T0 cardinality
  -> finite disjoint sums / finite union upper bounds
  -> closed-open lower and upper rank inequalities
  -> exact finite complement at a finite ordinal tail.

Closed lattice of X
  -> finite unions of principal downsets describe closed sets of H X
  -> H X is Noetherian
  -> functoriality under continuous surjections
  -> finite discrete extension estimate
  -> transfinite induction proving A.

Known published topological product formula (GL23, Theorem 10.9)
  + A + finite-support bouquets + binary/natural-product identity
  -> all-ordinal T1 witnesses B.

Closed lattice at omega+n
  -> unique infinite closed core of rank omega
  -> remove at most one core generic point, preserving the closed lattice
  -> pass to the finitary closed powerspace, preserving its closed lattice
  -> finite downset-indexed cells plus finite exceptional points
  -> finite-cell rank lemma
  -> necessary formula in C.

Explicit topology with a countable cofinite core and a finite poset Q
  -> every pair (Q,U) occurs
  -> sufficiency in C.

## Delicate points checked during preparation

1. Stature is the rank of the top closed set, NOT the rank of the whole
   closed-set poset. H(empty) is a singleton of stature one.
2. The lower bound uses ordinary LEFT addition: 1+alpha, not alpha+1.
3. Finite stature forces finite cardinality only after taking T0.
4. Every subspace of a Noetherian space is Noetherian, using the closure
   embedding of its closed-set lattice into that of the ambient space.
5. The closed-open lower bound uses the interval [F,X] and ordinary ordinal
   addition; the upper bound uses natural sum and a continuous sum map.
6. The finite slices of H(F) x H(D_n) need not be closed. The union bound
   works for arbitrary finitely many subspaces, so this is not an issue.
7. At a limit alpha, ordinal 2^alpha is a pure omega-monomial. Finite natural
   sums of smaller ordinals remain below it. A finite coefficient cannot
   be suppressed at a successor input.
8. The closed-normal-form proof does not assume H X is already Noetherian:
   a decreasing ordinal weight on finite maximal-generator antichains
   establishes well-foundedness first.
9. In the omega+n core, not every point initially has finite closure.
   A core generic point can exist. It must be removed by a proved
   closed-lattice isomorphism before enumerating finitary powerspace points.
10. Non-finitary points such as F union J, J subset U, can still generate
    closed subsets of the full powerspace. Taking their traces supplies
    the pure-cell unions needed in the finite-cell lemma.
11. The finite-cell rank lemma needs finite closures of cell points AND
    closedness of all downset unions of cells. Both are verified.
12. At countable limit construction stages, the bouquet has countably many
    countable components, so the claimed countability is preserved.
13. The equivalence of the old-bound criterion with omega^omega divisibility
    concerns ORDINAL multiplication and the exponents of Cantor normal form.
14. The independent finite-model count is not used to infer a transfinite
    rank by taking a numeric limit; doing so would lose coefficients.

## What the executable program checks

It exhausts finite posets through six points up to relabeling by linear
extensions (with repetitions), computes all distinguished downsets, and
records the finite data occurring in the spectrum theorem. Separately it
builds finite-core realizations and checks 1,221 downset counts for cores
of sizes 1,2,3 and posets through size four.

## Remaining uncertainty and scope

The arguments have been internally checked, not independently refereed.
No external mathematician or theorem prover has verified them as part of
this task. The binary wqo bound is prior work, not a new theorem here.
The priority of its extension to arbitrary Noetherian spaces, the T1
realizations, and the full finite-tail spectrum has not been established
by an exhaustive literature review. The general spectrum at arbitrary
ordinals remains beyond the results of this manuscript.
