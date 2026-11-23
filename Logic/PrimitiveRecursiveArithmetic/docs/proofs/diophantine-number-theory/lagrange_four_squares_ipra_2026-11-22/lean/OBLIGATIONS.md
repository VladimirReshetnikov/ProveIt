# Formalization obligations and proof order

The entries below are proof obligations, not statements claimed to have passed
Lean. The report proves their mathematical content and explains their iPRA
translation. `FourSquares.lean` implements their functions and conditionally
assembles the final theorem from the six fields of `ArithmeticContracts`.

## A. Primitive arithmetic and bounded search

1. **Search correctness.** `firstLt test B ≤ B`; if its value is below `B`, its test
   succeeds; if a test succeeds at some `j < B`, the returned value is below `B`;
   every smaller index fails. Prove these from the recursive definition, using a
   Boolean prefix fold for the corresponding iPRA induction invariant.
2. **Bounded conjunction.** `allLt test B = true` iff every `test j` with `j < B`
   is true. The host statement may be quantified; its object proof uses the
   characteristic function of the bounded statement.
3. **Euclidean arithmetic.** For a positive natural modulus, division gives a
   quotient and remainder; exact divisibility identifies the quotient. Prove
   positive-factor cancellation, the remainder bounds, and their signed-code
   counterparts. Division by zero is total but is never used by a valid step.
4. **Bounded primality facts.** If `IsPrime p`, then `2 ≤ p` and every positive
   divisor below `p` is one. Conversely, no divisor in `[2,p)` means the Boolean
   primality test succeeds. Prove Euclid's prime divisor lemma by a bounded
   Euclidean algorithm / Bezout computation, as detailed in the report.
5. **Least divisor.** If `2 ≤ n`, then `p = leastDivisor n` satisfies `2 ≤ p ≤ n`,
   `p ∣ n`, and `IsPrime p`. A proper divisor of `p` would be a smaller eligible
   divisor of `n`; no prime factorization theorem is required.

## B. Finite counting and the seed

6. **Square-residue injectivity.** For odd prime `p`, write `h = (p-1)/2`. If
   `a,b ≤ h` and `a² ≡ b² (mod p)`, Euclid's lemma applied to
   `(a-b)(a+b)` gives `a=b`. Both factors are strictly bounded in absolute value
   by `p`; the `a+b=0` case also gives `a=b=0`.
7. **Finite image counting.** An injection from an explicitly supplied list of
   `p+1` entries into the `p` residues is impossible. Implement occurrence counts
   and sum them in the two finite orders. This is bounded finite arithmetic, not
   a principle about arbitrary infinite sets.
8. **Seed existence.** The `h+1` distinct residues `a²` and the `h+1` distinct
   residues `-1-b²` must meet. Thus one of the `(h+1)²` lexicographically searched
   pairs satisfies `p ∣ a²+b²+1`.
9. **Seed bounds.** For the first such pair, `S=a²+b²+1` is positive and
   `S ≤ 2h²+1 < p²`. Exact quotient `m=S/p` therefore satisfies `0<m<p`, and the
   tuple `(a,b,1,0)` has norm `mp`. Treat `p=2` by `(1,1,0,0)`.

Together A.1--A.4 and B.6--B.9 construct `ArithmeticContracts.seed_sound`.

## C. Euler multiplication and even descent

10. **Euler identity.** Expand the four polynomial coordinates of `Z4.mul` and
    verify `normSq (mul x y) = normSq x * normSq y`. Also prove conjugation
    preserves the norm. A host `ring` proof is convenient; the object proof is a
    fixed polynomial identity over signed natural codes.
11. **Parity pairings.** If a tuple has even norm, it has an even number of odd
    coordinates. The three explicit pairings used in `evenHalf` therefore always
    pair equal parities. The first branch pairs `(a,b)` and `(c,d)`; the second
    `(a,c)` and `(b,d)`; the third `(a,d)` and `(b,c)`.
12. **Halving identity.** For equal-parity integers `u,v`, both `(u+v)/2` and
    `(u-v)/2` are exact integers, and the sum of their squares is
    `(u²+v²)/2`. Applying this to the two pairs halves the norm. If the old
    multiplier `m>1` is even, the new multiplier is `m/2`, positive and below `m`.

## D. Odd descent

13. **Centered residue.** For positive odd `m`, `r=centered m z` satisfies
    `r ≡ z (mod m)` and `|r| ≤ (m-1)/2`. This follows from the Euclidean remainder
    and the explicit branch condition `2*r ≤ m`.
14. **Remainder norm quotient.** For `PrimeState p s`, centered residues satisfy
    `m ∣ normSq r`. Let the exact nonnegative quotient be `k`.
15. **Positive quotient.** If `k=0`, all four residues vanish. Every old coordinate
    is a multiple of `m`, so `m² ∣ mp` and cancellation gives `m ∣ p`. This
    contradicts `1<m<p` and primality. Therefore `k>0`.
16. **Strict quotient.** Since `m` is odd, `normSq r ≤ (m-1)² < m²`, so `k<m`.
    Splitting off the even-multiplier case is essential to this strict bound.
17. **Exact coordinate divisions.** Let `z=mul x (conj r)`. Modulo `m`, its scalar
    coordinate is `normSq x`, hence zero, and its three vector coordinates are
    alternating expressions that cancel. Thus every coordinate is divisible by
    `m`, exactly as `Z4.divide` requires.
18. **New norm.** Euler's identity gives
    `normSq z = (mp)(mk) = m²(pk)`. Dividing the four coordinates by `m` and
    cancelling `m²` gives norm `pk`. The new multiplier is therefore again
    positive and below `p`, and is strictly below the old one.

C.10--C.12 and D.13--D.18, with the absorbing `m≤1` branch, construct
`ArithmeticContracts.descent_preserves` and `descent_decreases`. The latter uses
the saturated rank `m-1`: at `m=1` it is zero; otherwise strict decrease of `m`
implies `newRank ≤ oldRank-1`.

## E. Loop assembly already expressed in the scaffold

19. **Generic preservation.** `iterate_preserves` supplies its proposed proof by
    ordinary host induction on the explicit fuel.
20. **Generic rank bound.** `iterate_rank_bound` supplies its proposed proof of
    `rank(iterate step t s) ≤ rank(s)-t`. It uses only the stated preservation and
    saturated-rank decrease assumptions. Its arithmetic subgoal uses `omega`.
21. **Prime termination.** Initial `m<p` and `p` steps force the final rank to
    zero. Positivity then gives `m=1`. `primeRep_correct` expresses this assembly.

These scripts remain uncompiled, like the rest of the Lean file. For an iPRA
derivation, instantiate the invariants as quantifier-free formulas on encoded
states; do not infer the restriction merely from Lean's general induction rule.

## F. General natural numbers and output

22. **Factor-step invariant.** Assuming the prime representation theorem, the
    least-divisor facts and Euler identity preserve
    `remaining * normSq accumulated = original_n`, with positive remainder.
    This proves `ArithmeticContracts.factor_preserves`.
23. **Factor rank.** If `remaining>1`, its least divisor is at least two, so exact
    division gives a positive strictly smaller remainder. At remainder one the
    transition is absorbing. This proves `factor_decreases` for rank
    `remaining-1`.
24. **Final remainder.** `n` iterations from remainder `n>0` give rank zero, hence
    remainder one and accumulated norm `n`. The direct zero case completes
    `signedFourSquares_correct`.
25. **Absolute values.** For each integer `z`, `((z.natAbs : Nat) : Int)^2 = z²`.
    Summing four identities proves `ArithmeticContracts.naturalize_norm`.
26. **Final target.** Injectivity of `Int.ofNat` gives `fourSquares_correct`.
    Four existential introductions give `lagrange_from_contracts`.
27. **Optional witness bound.** The norm equality implies each natural coordinate
    is at most `n` (and at most `⌊√n⌋`). The bound by `n` needs no square-root
    function: `a≥1` implies `a≤a²≤n`, while `a=0` is immediate.

## G. Remaining syntax-level work

28. Fix an explicit iPRA syntax/derivation implementation (or reuse the reviewed
    ProveIt implementation with an exact pinned source reference).
29. Add natural-code definitions for the finite program, with defining equations
    for composition and primitive recursion. Do not assume a primitive recursive
    universal evaluator for arbitrary primitive recursive programs.
30. Prove the Boolean-prefix, arithmetic, and loop lemmas as object-theory
    derivations using only quantifier-free induction; assemble the identity for
    the four output function symbols.
31. Prove the correspondence of the encoded functions with the host definitions.
    The resulting final object-theory theorem should state derivability of the
    output identity, and then of its universally quantified existential closure.

These final syntactic derivations are a separate obligation. A complete ordinary
Lean proof of the natural-number theorem, even after all earlier contracts are
discharged, does not by itself finish them.
