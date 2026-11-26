# Independent review of the intermediate genus-field certificate

Reviewer: transfer_research agent. Files reviewed: `genus_transfer.tex`, `genus_certificate.py`, `genus_certificate.json`.

Outcome: no mathematical error found in the stated theorem, rank lemma, four numerical exclusions, or demonstration discriminant. The proof is a human mathematical proof; the script checks only the finite arithmetic it explicitly claims to check.

## Algebraic argument

1. For a finite abelian class group of exponent dividing 2m with m odd, its square subgroup has odd exponent, and the natural map A[2] -> A/A^2 is both injective and surjective. The stated proof using a^m and a^(1-m) is valid.
2. For an imaginary quadratic fundamental discriminant D with t distinct rational prime divisors, the genus field has degree2^t over Q and is unramified over K. Fixing the image of a k-dimensional H gives degree2^(t-k) overQ. The discriminant tower formula gives |Delta_F|=|D|^[F:K] with no missing finite ramification factor.
3. Frobenius identity [p]=h*a^2 gives [p]^m=h. The product of ideals p^m J is principal because h^2=1. J is inserted after exponentiation; its norm cost is R, not R^m.
4. Distinct valuations m and0 at p and its conjugate show the generator is nonrational. The representation alpha=(a+b sqrtD)/2 with b a nonzero integer is valid for odd and even fundamental D. Its norm is at least |D|/4.
5. The ramified-class independence proof correctly treats the subtle prime2 case: if v2(D)=2, the unique possible nonempty relation is on all odd ramified primes; if D is odd or v2(D)=3, it is on all ramified primes. Consequently every subset of size at mostt-2 is independent. Injection into A/A² then follows from odd exponent of A².

## Primary table checks

The original Bach--Sorenson article was inspected from the author-uploaded full PDF:
https://www.researchgate.net/profile/Jonathan-Sorenson-2/publication/220576951_Explicit_bounds_for_primes_in_residue_classes/links/55100ea70cf2ac2905afbceb/Explicit-bounds-for-primes-in-residue-classes.pdf

Theorem5.1 on p1729 gives (4 logDelta+2.5n+5)^2. Table3 on p1731 is for baseQ and contains:

- n3--4, logDelta25--100: (2.035,0.27,5.3).
- n3--4, logDelta100--1000: (1.527,0.17,6.4).
- n5--9, logDelta100--1000: (1.629,0.11,6.1).
- n15--49, logDelta100--1000: (1.745,0.04,5.8).

All four affine bounds and their degree/discriminant ranges in the manuscript agree. The n4 envelope for y>=50 is larger than the new row's bound, so retaining it is safe. The derivative test for (ay+b)^6 exp(-y) is used with the correct direction.

The EKN primary PDF https://arxiv.org/pdf/1803.02056 independently confirms432 exponent-six fields through3.1e20 and the ERH upper bound2.5e25. These are inherited external inputs, not recomputed here.

## Code checks

Executed `python3 notes/genus_certificate.py` and compared its output byte-for-byte with `notes/genus_certificate.json`; they match. The exponential-series tail bound is valid (positive first omitted term and a dominating geometric ratio). All table ratios are strictly below1 as asserted. Trial division certifies both1000000007 and1000000009. The discriminant D=-4 rad with rad squarefree and congruent2mod4 is fundamental. Its seven prime divisors, cofactor and productP5=2310 agree with the text.

## Scope

The new inequalities exclude extra families from the unresolved window relative to the earlier packet. They do not establish a complete432-field classification. They use a new genus-field refinement combined with the exported Dirichlet GRH, rather than transferring the original theta-lift construction to another L-function family. The manuscript makes these limits explicit and should retain them.
