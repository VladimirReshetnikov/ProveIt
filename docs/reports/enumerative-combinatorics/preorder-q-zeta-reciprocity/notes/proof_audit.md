# Proof audit (merged)

This is a local audit of the written arguments, not independent peer review or
proof-assistant certification. Section, theorem and lemma numbers refer to the
merged `article.tex` / `article.pdf` in this directory.

## Logical dependency map

### Shared foundation

1. Hall's theorem (Appendix A) identifies feasible preorder lattice points with
   integral allocations of unit resources (Lemma 2.2). Support-function
   separation gives the Minkowski realization with an auxiliary capacity
   (Lemma 2.1).
2. Reflexivity proves that maximal feasible vectors have total n; coordinatewise
   closure gives product-of-chains intervals and hence `cov(a) = |supp(a)|`
   (Lemma 2.3). A matching-free alternative proof by tight ideals is recorded in
   Remark 2.4, because the second proof must not depend on Hall's theorem.
3. Postnikov's Theorem 11.3 plus the filter identification of draconian vectors
   gives the independent-capacity enumerator `E_sigma(u,v)` (Prop. 5.1), whose
   `v = 0` case is the weighted dual lattice-count polynomial `L_{tau*}`
   (Prop. 5.2). Interior translation plus Ehrhart reciprocity gives
   independent-capacity reciprocity in all n+1 variables (Prop. 5.4) and, along
   a fixed ray, `L_{tau*}(-c) = (-1)^n #int Q_{tau*}(c)` (Cor. 5.6).

### Proof A (Sections 3, 6, 7, 8)

4. Weighted incidence matrices evaluate the q-zeta polynomial at `[-1]_q` as an
   inverse square (Lemma 3.1), for an arbitrary finite poset with least element
   and an arbitrary normalized height. The Möbius function localizes the
   evaluation onto the signed Boolean sums `eta(B)` (Prop. 3.3).
5. **Engine 1.** The support-restricted graph `G_T` identifies its left
   draconian sequences with maximal points supported in T and its right
   sequences with interior lattice points at capacities `1+1_T`; Postnikov's
   bipartite duality closes the loop (Thm. 6.1). A two-value interpolation
   table (Lemma 7.1) and a Bernstein-type collapse then give Theorem 1.1.
6. **Engine 2.** Subtracting `1_B` replaces the resources by `E \ B`
   (Lemma 8.4); transitivity lets the residual targets outside B be privatized
   without changing any Boolean feasibility test (Lemma 8.5); maxima with
   support B correspond bijectively to distinct full-allocation degree vectors
   of the residual graph (Lemma 8.6); and the private-element Euler identity
   (Lemma 8.2), proved from two applications of Postnikov's Theorem 11.3 plus
   Ehrhart reciprocity, evaluates the alternating count. This engine uses
   Theorem 11.3 only, and thereby proves, in the case it needs, the duality
   Engine 1 imports.

### Proof B (Sections 9, 10)

7. Setting `v = 0` in Prop. 5.4 makes the binomial factor
   `binom(n-|a|-1, n-|a|)` annihilate every non-maximal layer (Prop. 9.1).
   There is no polytope "of capacity -1" anywhere; the selection is a pure
   algebraic specialization.
8. Multilinearity and the basis `(1-z)^m` convert that identity into the
   coefficient-transfer theorem for `T f(z) = (1-z) f(-z/(1-z))` (Thm. 9.2),
   valid for arbitrary families of formal power series.
9. Feeding `f_i(z) = (1-z)(1 - z_i z)` gives Theorem 1.1 again, and its
   coefficient form is a third, independent derivation of the exact-support
   identity (Section 9.3).
10. The Gaussian endpoint formula (Prop. 9.4), valid at every integer m, plus
    the local negative kernel (Lemma 9.6) connect the transfer theorem to
    `Z_q` without using Section 3 at all; feeding `prod_{j=0}^r (1 - t^j z)`
    then gives every `[-r]_q` (Theorem 1.2).

No theorem asserted by another report in the user's manifest is used. Hall's
theorem, Postnikov's theorems and Ehrhart reciprocity are imported, not
reproved, except that the finite Hall theorem is proved in Appendix A for the
sake of fixing conventions.

## Delicate transitions checked

The article's Section 15.2 lists thirteen numbered points. The ones most
likely to hide an error:

**Negative argument and the -2 exponent.** The multichains have m-1 entries, so
m = -1 corresponds to the matrix power -2, not -1. For general normalized
heights the incidence matrix has scalar blocks indexed by distinct heights,
with pairwise distinct eigenvalues over Q(q); the filtration proves a
*squarefree* annihilating polynomial, so there are no Jordan blocks and the
argument does not rely on upper triangularity alone. The independent
multichain-interpolation tests were designed to catch an error here.

**Boolean localization.** Only the middle vector a is forced Boolean by
mu(0,a). The vector `a + 1_S` may contain 2s and must not be treated as
Boolean; the signed count does not discard those terms.

**Postnikov's shift.** The untrimmed formula for an auxiliary full simplex has
`binom(y_0+a_0, a_0)`, not `binom(y_0+a_0-1, a_0)`. At weight zero its factor
is 1 for every allowed a_0. Checked against Theorem 11.3 on printed page 28 of
the arXiv PDF. The new 0-coordinate is kept, so the draconian total is n and
not n-1.

**Dual orientation.** The weighted count uses `D_tau(i)`, not `U_tau(i)`;
checked twice, in Prop. 5.1 and again in the support-restricted graph of
Section 6.

**Evaluation at -1.** All non-full-simplex binomial factors at t = -1 are 1,
-1 and 0 as `a_u` equals 0, 1 or at least 2. The surviving Boolean vectors are
exactly the Hall-matchable subsets.

**Interior and dimension.** In Engine 1, the capacity `1+1_T` gives
`y(I) <= |I∩T| - 1`, not `<= |I∩T|`. In Engine 2, the private elements
contribute the full cube `[0,1]^R`, making K full-dimensional, and the shift by
`1_R` removes that cube and leaves the *strict* bounds `y(J) <= |N(J)| - 1`.
The second Postnikov application counts those vectors; it does **not** assert
an affine bijection between polytopes of different ambient dimensions.

**Multiplicity.** The final objects are distinct allocation degree vectors.
Counting maps or matchings with multiplicity would give the wrong theorem,
which is also why the dynamic program in Section 14.3 must deduplicate.

**Preorders, not just partial orders.** Privatization uses reflexivity and
transitivity, never antisymmetry. Genuine equivalence classes are allowed and
must retain their individual coordinates. The exhaustive verifiers include
them, and include relations with genuine cycles.

**Boundary cases.** Empty E, empty residual resource set and empty target sets
are handled with the empty vector and the empty allocation. A resource with no
nonprivate neighbour makes the alternating sum cancel by toggling its private
element and makes a full allocation impossible, so no empty simplex is ever
passed to the nonempty-simplex formula. The support-restricted graph is checked
for isolated vertices before connected bipartite duality is invoked.

**Height statistic.** The refined exponent is `h(1_supp(b))`, not `h(b)`. The
nonlinear-height test on the three-element chain distinguishes the two
choices.

**Capacities stay independent.** In Proof B reciprocity is established in all
n+1 variables first, and only then is v set to 0.

**No unwarranted extrapolation.** The pure downset `down(1,1,1) ∪ down(3,0,0)`
violates both the supportwise identity and the transfer identity, despite
containing the Boolean cube and having all maxima of rank three; the reflexive
nontransitive three-source system violates the support formula despite having
a transport representation; and a single coordinate of capacity two violates
it despite everything else. The article does not assert the result for
arbitrary pure downsets, for arbitrary assignment systems, or at arbitrary
capacities, and asserts neither log-concavity of the support polynomial nor a
direct sign-reversing involution.

## Cross-validation and its limits

The exact-support identity has three independent derivations in this document
and the headline theorem has two independent proofs. That is genuine
cross-validation of the internal reasoning: an error in the incidence
inversion, in either geometric engine, or in the transfer involution would
break one route and not the others.

It is **not** validation of the reading of the source. All three routes start
from the same transcription of the conjecture, of the q-zeta normalization
with m-1 chain entries, and of the `cov` statistic; a shared misreading there
would not be caught by their agreement. Those conventions are therefore stated
explicitly in Section 1 and audited in Section 15.

## Verification limits

The Python checks are exact finite tests. They can expose indexing errors,
sign errors, or counterexamples at the tested sizes; they do not certify the
arbitrary-size theorems or their novelty. The full proofs still warrant expert
review, especially the two specializations of the imported polyhedral formula
and the imported bipartite duality.
