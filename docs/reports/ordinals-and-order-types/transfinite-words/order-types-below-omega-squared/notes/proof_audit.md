# Proof audit and intended referee checklist

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

## What the software verifies

The suite compares greedy and nondeterministic endpoint deciders, tests proper
and universal product maps against componentwise comparisons, tests padding
reflection and limit lengths, and checks the universal-only classification.
All omega blocks use exact symbolic semantics. Finite truncation is never used.

The reference decider shares the same proved semantics. It is not an independent
formalization of ordinal functions. Tests cannot establish an unbounded ordinal
supremum, a maximal linear-extension theorem, or novelty of the result.

## Remaining external verification

The article has no deliberately unproved nonclassical lemma in its main
argument. It remains unrefereed and has not been checked in Lean or another
proof assistant. An expert should check the product-reflection lemmas first,
then the classical theorem hypotheses and the selected-family induction.
