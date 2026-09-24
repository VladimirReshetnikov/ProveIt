# Proof status and assumptions

## Main proposed contributions

**Theorem 4.4 — Exact normal-form discrepancy.**
For the surreal map J induced by an elementary embedding j: V -> M with
critical point kappa, and its canonical strongly additive exponent lift T,
the equalizer of J and T is exactly F_kappa, the class of surreals with
normal-form support of cardinality less than kappa. The normal form of J(x)-T(x)
is the complementary subseries indexed by j(mu) \ j``mu; when nonempty, its
first index is kappa.

Assumptions: transitive target, uncountable critical point, Separation and
Replacement for the map, and the standard Conway normal-form foundations.
A normal-measure ultrapower supplies a set-parameter-definable witness.
Lemma 2.2 proves the normal-form absoluteness needed in the argument.

**Theorem 7.3 — Almost-disjoint omnific independence.**
For any uncountable kappa, a kappa-almost-disjoint family in [kappa]^kappa
gives algebraically independent masks over the entire F_kappa. The coefficient
field is not restricted to the selected exponent group. The proof annihilates
the rational span of all polynomial coefficient supports with private
coordinate functionals, then singles out a unique nonzero coefficient using
maximum total degree.

Assumptions: ZFC, classical Hahn-field arithmetic, and the specified
almost-disjoint family. No large cardinal is used.

**Theorem 7.5 — Maximal cardinality in a fixed Hahn field.**
Under 2^{<kappa} = kappa, there are 2^kappa independent positive purely infinite
omnific integers in a set-sized Hahn field K_kappa. The relative transcendence
degree of F_kappa K_kappa over F_kappa is exactly 2^kappa.

Assumptions: those of Theorem 7.3 plus the stated cardinal arithmetic.
The conclusion therefore applies at measurable cardinals, but also at other
cardinals satisfying that equation.

## Consequences and explicit encodings

- Theorem 5.1: the induced map preserves all strong sums indexed by fewer than
  kappa elements, and explicit kappa-sized monomial families witness failure.
- Theorem 5.2: for the strong lift, the locus of omega-map equivariance is
  exactly F_kappa; the specified monomial action cannot simultaneously extend
  to an everywhere omega-equivariant and kappa-strong map.
- Theorem 6.1: the equalizers restrict to the omnific integer part and extend
  to the algebraically closed field F_kappa(i).
- Theorem 8.1: one coefficient of the image of each omnific mask recovers the
  normal measure. The seed-ultrafilter theorem being encoded is classical.
- Theorem 8.4: measurability is equivalent, in the stated class setting, to
  existence of an ordinary ordered-field embedding with the specified
  omega-map, small strong-sum, and Hadamard-mask compatibility. The converse
  constructs a nonprincipal kappa-complete ultrafilter; it does not assume a
  set-universe embedding. The extra coefficient operation is essential to the
  statement as proved.
- Theorem 9.1 and Proposition 9.2: coefficient probes encode derived seed
  ultrafilters, covering seeds, and exact seeds. The ensuing strong compactness
  and supercompactness principles are standard ultrafilter characterizations
  in numerical coordinates, not new consistency-strength results.
- Theorem 10.2: the omnific prefix-tree principle is a coding of the classical
  tree characterization of weak compactness at inaccessible cardinals.

## Standard foundations, not claimed new

Conway normal forms, truncation simplicity, Hahn convolution, real closure of
Hahn fields over the reals with divisible exponent group, cardinal-bounded
Hahn fields, canonical exponent lifts, real-closed/algebraically-closed field
quantifier elimination, and the standard large-cardinal ultrapower and tree
principles are credited in the bibliography.

## Important distinctions

1. Agreement of J and T is not the same as either map fixing its input.
2. These are embeddings, not asserted to be automorphisms.
3. Support cardinality is not birthday and is not order-boundedness of support.
4. Every sum used is set-indexed; there are no proper-class sums.
5. Conway's omega-map is not the Gonshor exponential.
6. Strong sums are not defined as limits in the order topology.
7. Hadamard multiplication of masks is not ordinary surreal multiplication.
8. A zero measured coefficient does not imply the full discrepancy is zero.
9. A recovered normal measure does not by itself recover an arbitrary full
   elementary embedding or its target.
10. Pure field elementarity does not imply elementarity in an enriched birthday
    language or give an elementary self-embedding of the set universe.

## Verification boundary

All mathematical arguments in this article are written arguments and remain
subject to independent review. No Lean formalization is supplied or claimed.
No finite numerical experiment is used as evidence for large-cardinal existence.
The manuscript does not certify priority or claim a named longstanding
conjecture has been resolved. Document compilation, cross-reference checks,
and visual PDF inspection do not change that mathematical status.
