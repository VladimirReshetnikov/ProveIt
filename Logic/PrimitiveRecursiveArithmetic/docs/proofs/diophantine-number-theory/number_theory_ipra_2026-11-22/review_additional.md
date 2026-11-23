# Follow-up audit: foundational repair and algebraic chapter

Reviewed the updated `chapters/foundations.tex` and the new `chapters/algebraic.tex`. This review concerns the displayed mathematical arguments and their compatibility with the proposed primitive recursive proof discipline. It is not a Lean compilation or an independent check of object-theory derivations.

## 1. Foundational circularity is repaired

The revised proof of bounded Boolean reflection now constructs the Boolean search directly. Its guarded quantifier-free invariants are sufficient:

- `F(j)=1 -> w(j)=t`;
- `F(j)=0 -> w(j)<j and b(w(j))=1`;
- for a fixed parameter `i`, `i<j and b(i)=1 -> F(j)=0`.

For the first two invariants, the induction is guarded by `j <= t`. When `j < t` and the old failure product is zero, the old successful index is strictly below `j`, hence cannot equal the sentinel `t`; the update retains it. If the old failure product is one, the stored index is the sentinel, and the next Boolean test either retains failure or selects the current index. The induction step beyond the bound is vacuous because of the guard. The product is Boolean by the same elementary product argument already given.

Thus a zero final failure product yields a numerical witness, and an existing bounded witness forces that failure product to vanish. The later bounded-search lemma may now legitimately invoke the already-proved bounded reflection to prove leastness and failure characterization. There is no remaining dependency cycle in these two lemmas.

The universal-reflection proof is also properly arranged: its forward induction keeps one candidate index as a parameter, and its reverse induction uses the quantifier-free assertion `j <= t -> P(j)=1` while retaining the fixed bounded universal premise as an open assumption.

## 2. Algebraic norm and nonunique factorization: sound

The coordinate multiplication and norm identity are correct. Norm zero detects the zero pair, norm-one elements are exactly the two stated units, and direct substitution gives the monic quadratic polynomial. Norm multiplicativity also supplies cancellation of the possible zero-factor cases needed by the irreducibility arguments.

The irreducible factorizations of 6 are correctly distinguished. A proper factorization of norm 4, 9, or 6 respectively requires the forbidden norm patterns (2,2), (3,3), or (2,3). No norm-2 or norm-3 element exists. The failure of primality of 2 follows from coefficientwise parity. These are bounded numerical arguments and require no ambient complex field, ideals, or unique-factorization machinery for a general ring.

## 3. Truncated valuations: sound, with a small clarity improvement

The multiplication formula and ultrametric inequality are correct, including zero inputs and precision `k=0`. For unequal truncated valuations `r < s`, one has `r < k`, so writing `a=p^r u` does give `p` not dividing `u`. One may always write `b=p^s v`, even if `s=k` and its untruncated valuation is larger. No condition on `v` is needed, because `s-r >= 1`.

For clarity, introduce `r=v_(p,k)(a)` and `s=v_(p,k)(b)` afresh when starting the sum proof, and explicitly say that in the branch `r<s` only the residual factor `u` must be nonzero modulo `p`. The current proof's sentence about both residual factors being nondivisible by `p` belongs to the earlier uncapped multiplication branch, and should not appear to be an assumption in the capped sum branch. This is a scope/notation clarification, not a false formula.

## 4. Taylor congruence and Hensel lifting: sound

The condition `k>=1` correctly ensures `2k>=k+1`, including the case `p=2`. The inverse derivative determines exactly one digit modulo `p`, and the residue bounds give the unique representative below `p^(k+1)`.

The Taylor congruence first implies divisibility of `f(b)` by `p^k`, so its quotient in the lifting proof is exact; then the congruence of that quotient modulo `p` proves the next level of divisibility. Polynomial congruence preserves the nonzero derivative modulo `p` at every later stage. The compatible-name construction is primitive recursive and its stated uniqueness is properly explained as a first-order schema for any other supplied fixed primitive recursive sequence, without quantification over arbitrary functions inside iPRA.

The numerical example is correct: for `X^2-2`, the residues 3, 10, and 108 are roots modulo 7, 49, and 343, respectively, and each reduces to the preceding residue.

## 5. Partitions: sound, with an empty-case convention to make explicit

The partition recursion is correct, including `m>n` when its second term is suppressed by the indicator. The truncated generating product counts all relevant multiplicity vectors and introduces no infinite formal series. The binary odd-parts/distinct-parts correspondence is a genuine inverse bijection, and its data bounds follow from weight preservation.

The conjugation proof is the usual finite double-counting involution and is valid. To make the theorem literally cover `n=k=0`, explicitly define the largest part of the empty partition to be 0. Then for `n>0, k=0`, both counted classes are empty; for `k>n`, they are also both empty. These two boundary statements complete the unrestricted numerical statement without changing its proof.

## Conclusion and limits

No substantive mathematical or iPRA gap was found in the repaired foundation or the reviewed algebraic chapter. The two recommended edits concern scope of the truncated-valuation variables and the convention for the largest part of an empty partition. Full Lean compilation and syntactic derivation checking remain outside this review.
