# Proof audit and intended referee checklist

This note accompanies the merged report. The article merges two independently
produced research reports, `order-types-below-omega-squared` and
`guarded-periodic-blocks`. The shared core theorem is proved once. Two steps
carry two proofs on purpose, and they are listed under "Two preserved
alternative arguments" below.

## The four boundaries to check independently

A hidden gap would have to sit at one of these four points.

1. Embeddings are STRICTLY increasing on ordinal positions. Without strictness,
   cofinal consumption of a target block fails and cofinal localization is false.
2. A newly introduced downset is contained in NO old downset. Mere distinctness
   is not enough; the article gives a worked two-letter counterexample.
3. Exclusion applies to the EXPLICIT PURE PERIODIC SEGMENT of a displayed
   separator, not to the finite prefix that may precede it inside the same
   canonical block. This is the ordinal identity k + omega = omega.
4. Full support needs an EARLIER PROPER support, so that a guard of positive
   limit length can be built. Without one the exceptional value H_n * omega is
   the truth.

Points 2 and 4, and guarding altogether, are exercised as executable negative
controls in the test suite; each control asserts that the naive encoding FAILS
to reflect the componentwise order.

## Two preserved alternative arguments

- Monotone surjection (classical input (ii)). One argument injects the target
  bad-sequence tree into the source tree; the other orders the fibres of the
  surjection along a maximal linear extension of the target and linearizes each
  fibre. Both are recorded. The first also yields the wqo assertion; the second
  exhibits a concrete linear extension and is reused by the exact-length bounds.
- Product amplification. The main line imports the de Jongh-Parikh natural
  product formula o(X x Y) = o(X) (x) o(Y) and runs the induction on natural
  powers. The alternative route proves o(X^r) >= o(X)^r by hand, ordering
  r-tuples on their last unequal coordinate, and uses only ordinary ordinal
  exponentiation with sup_r H_q^r = H_(q+1). What the alternative buys: the main
  theorem then needs no product-theorem import at all. The natural product, and
  the natural sum, are still genuinely needed for the exact-length section, which
  is supplementary and may be skipped by a referee checking the two-letter
  question.

## Exact hypotheses

1. P is a finite poset. For a finite quasi-order, first quotient equivalent labels.
2. Word lengths are strictly below omega^2, so each finite code has only finitely
   many displayed omega tokens.
3. Position maps are strictly increasing; no continuity is assumed.
4. Label comparisons follow the order on P, not literal equality unless P is an
   antichain.
5. Periodic block D repeats a nonempty downset D. Downward closure is crucial to
   the excluded-letter arguments.
6. Maximal order type is taken after quotienting mutual embeddability.
7. The periodic representative may repeat all of D or only Max D; the two words
   are mutually embeddable and the article fixes the all-elements convention.
8. The guard map may or may not be applied to the final component. Both the
   all-guarded and the unguarded-final variants are order embeddings of the same
   Cartesian power; the article fixes the unguarded-final form in the main text
   and records the all-guarded form in its quick-reference appendix.

## Critical local arguments

### Cofinal localization

The indices of finitely many target tokens visited by a source omega block form
an eventually constant nondecreasing sequence. Its final token is infinite and
the image is cofinal there. All recurrent source labels belong to its downset.
Any later source position must occur after that target token.

This does not imply the whole source omega block stays in one target token.
Initial finite pieces are allowed to straddle earlier blocks.

### New marker synchronization

For a newly introduced D, require D not contained in E for every old E. Merely
requiring D != E is insufficient. Cardinality ordering of distinct downsets
provides the needed condition. The new source markers have a strictly increasing
injection of cofinal destination indices into the equal-size target marker set;
that injection must be the identity.

### Proper marker reflection

Use components separated by c B_D, where c is outside D. Previous synchronized
cofinality gives the lower boundary. The source guard cannot lie in the next
target B_D, so it lies in the target component plus its final guard. Everything
before the source guard lands in the target component itself. The guard need
not match the displayed target guard exactly.

### Cancellable limit padding

G(u) = u c B_E, with E proper and c outside E. In an embedding G(u) <= G(v),
the source c cannot enter the final target B_E. All of u is therefore inside v.
Also len(G(u)) = omega*(k+1) if len(u) = omega*k + m, so G(u) has limit length.

### Universal marker reflection

All old blocks are proper; source B_P markers synchronize with displayed target
B_P markers. A padded component has all its images before any chosen image
point of the next source marker in the next target B_P. If the component had
any image point in that target B_P, infinitely many remaining component points
would need to fit below a finite bound inside one omega block. Impossible.
Hence the padded component lies in the corresponding padded target component;
reflection of G recovers the original comparison.

### Rigidity at equal block count

Under the ADDITIONAL hypothesis that source and target have the same number of
canonical omega-blocks, the i-th source block lies entirely and cofinally inside
the i-th target block, and the finite tail inside the finite tail. This is
strictly stronger than cofinal localization plus the straddling remark, and it
is NOT available in the main argument, where block counts differ by design. It
is used only for the exact-length strata and for canonical representatives.

### Canonical representatives

Normalizing each finite prefix by deleting its longest suffix contained in the
downset of the following block makes the finite representation unique: two
normalized token expressions are mutually embeddable exactly when they are
identical. The stack procedure never touches the final finite tail.

### Ordinal step

From X^(r+1) order-embedded in Y for every positive finite r, and o(X)=H_N,
obtain o(Y) >= sup_r omega^(omega^(N-1)*(r+1)) = H_(N+1). The independent
atom-count upper bound is H_(N+1). This does not assume maximal order type
commutes with increasing unions.

## Deliberately handled exception

With the universal block as the only infinite token, every expression is
B_P^k v with v finite, up to equivalence. Comparison is ordered first by k,
then by finite-word embedding at equal k. Thus the type is H_n * omega, not
H_(n+1). For n=1 this gives omega^2. For the full family and n>=2 there is a
proper nonempty downset, so limit padding repairs exactly this obstruction.

## The exact-length warning

Each individual length stratum has an exactly computed maximal order type, and
the supremum of those values over all lengths is omega^(omega^n). That is
STRICTLY BELOW the answer omega^(omega^(n+j-2)) for n >= 2, because a linear
extension of P already supplies n+1 distinct downsets, so j >= n+1. The strata
are not ordinal-sum layers: a shorter word need not embed into a longer one, so
a maximal linear extension may interleave strata. The main theorem therefore
cannot be obtained stratum by stratum, which is exactly why the supremum in the
main induction is a supremum of lower bounds on ONE fixed order rather than a
supremum of the types of pieces.

## What the software verifies

The suite compares greedy and nondeterministic endpoint deciders, exhaustively
over the whole two-letter token domain up to length four and on small posets,
tests proper and universal product maps against componentwise comparisons,
tests every allowed support subfamily of both binary alphabets, tests padding
reflection and limit lengths, checks the universal-only classification, checks
that normalization preserves both the class and every decided relation and that
mutually embeddable expressions have identical normal forms, checks the
fixed-length product decomposition, and runs the three negative controls.
All omega blocks use exact symbolic semantics. Finite truncation is never used.

The reference decider shares the same proved semantics. It is not an independent
formalization of ordinal functions. Tests cannot establish an unbounded ordinal
supremum, a maximal linear-extension theorem, or novelty of the result.

## Remaining external verification

The article has no deliberately unproved nonclassical lemma in its main
argument. It remains unrefereed and has not been checked in Lean or another
proof assistant. An expert should check the product-reflection lemmas first,
then the classical theorem hypotheses and the selected-family induction.
