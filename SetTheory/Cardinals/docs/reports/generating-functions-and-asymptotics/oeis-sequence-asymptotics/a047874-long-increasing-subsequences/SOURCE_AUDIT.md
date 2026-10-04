# Source and novelty audit

Audit date: October 3, 2026 (Pacific time).
This is not an exhaustive literature search or a guarantee of priority.

## Current conjecture and established recurrence

Manuel Kauers and Chen Wang,
*Recurrences for permutations with long increasing subsequences*,
arXiv:2609.02220v1, submitted September 2, 2026.
https://arxiv.org/abs/2609.02220
https://arxiv.org/html/2609.02220v1

Section 1 defines regional D-finiteness as agreement with a globally
D-finite array. Theorem 1 proves the half-sector result. Section 1 also
derives the previously conjectured fourth-order A269021 recurrence.
Section 2 conjectures D-finiteness for every fixed sector k>=N/r and
asks for a uniform method. The article in this package proves that
existence statement. It does not prove the specific guessed r=3 operators.

Manuel Kauers and Christoph Koutschan,
*Some D-finite and some possibly D-finite sequences in the OEIS*,
Journal of Integer Sequences 26 (2023), Article 23.4.5.
https://arxiv.org/abs/2303.02793
Conjecture 17 is the older A269021 recurrence, already settled by the
September 2026 source. The package does not claim to settle it first.

## Established structural inputs

Alexei Borodin, Andrei Okounkov, and Grigori Olshanski,
*Asymptotics of Plancherel measures for symmetric groups*,
J. Amer. Math. Soc. 13 (2000), 481--515.
https://arxiv.org/abs/math/9905032

The v2 preprint (September 11, 1999) was inspected. Page 4 defines
D(lambda)={lambda_i-i} and the poissonized normalization. Theorem 2,
printed page 5, gives its determinantal correlations. Proposition 2.9,
printed page 16, gives the sum K(x,y)=sum_{s>=1}J_{x+s}J_{y+s}.
Those formula pages were visually inspected. No half-integer convention
was substituted silently.

Herbert S. Wilf and Doron Zeilberger,
*Rational function certification of multisum/integral/"q" identities*,
Bull. Amer. Math. Soc. (N.S.) 27 (1992), 148--153.
https://arxiv.org/abs/math/9207218

Section 2 specifies proper-hypergeometric factorial terms. Theorem 1 and
Corollary A give terminating multisum recurrence existence. The application
keeps j fixed, makes all factorial arguments affine, and makes support finite.

Christoph Koutschan,
*Creative telescoping for holonomic functions* (2013), pp. 171--194.
https://arxiv.org/abs/1307.4554

Theorem 2 and Section 4 give definite-summation closure, with treatment of
inhomogeneous boundary terms and parameter-dependent bounds. The proof in
this package does not assume that boundary terms automatically vanish.

Craige Schensted,
*Longest increasing and decreasing subsequences*, Canadian J. Math. 13
(1961), 179--191.
https://doi.org/10.4153/CJM-1961-015-3
Robinson--Schensted enumeration and its LIS interpretation are standard
inputs, not contributions of this package.

## OEIS identities and asymptotics

https://oeis.org/A047874 : exact LIS length array.
https://oeis.org/A214152 : LIS upper-tail array.
https://oeis.org/A269021 : upper-tail diagonal T(2n,n).
https://oeis.org/A267433 : exact-length diagonal A(2n,n).

A269021 and A267433 record the leading equivalent
16^n (n-1)!/(pi exp(2)), attributed to Vaclav Kotesovec, March 27, 2016.
A269021 still displayed a conjectural label on an old recurrence while
also linking to the 2026 paper proving it. The newer paper determines
its status, not the old label.

A267433 links to David Moews's proof of its leading equivalent:
https://math.stackexchange.com/questions/4771623
Answer September 22, 2023, revised September 25, 2023.
The full answer was inspected. It proves the leading asymptotic by a
hook-length/Plancherel concentration argument. This package credits that
result and independently develops uniform higher-order corrections.

## Repository scope

https://github.com/VladimirReshetnikov/ProveIt
Inspected revision: 6bf7f30d0352f7596e70928b3d4f304914075907.

Repository tools were used for the map, README, and targeted searches.
An exact-identifier search for A269021 returned no matches. This does
not rule out a differently named or unindexed prior report. A181280 was
rejected as a target after an existing report on it was found. A003238's
old leading-asymptotic conjecture label was not used as an open problem.
No repository files were changed or committed by this task.

## Claims requiring further review

The fixed-sector theorem and the uniform all-order extension are presented
with complete conventional proofs based on the named external results.
The numerical code does not establish the imported theorems or formalize
the full proof. Independent mathematical review remains appropriate.
There is no claim of global holonomicity of the original LIS array,
no full exponentially small transseries, no minimal recurrence orders,
and no proof-assistant/kernel certification.
