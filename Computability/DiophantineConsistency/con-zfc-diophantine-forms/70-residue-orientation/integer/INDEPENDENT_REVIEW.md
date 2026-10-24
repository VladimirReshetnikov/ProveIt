# Independent mathematical review of the affine orientation reduction

Review date: 23 October 2026. Comparison/source revision:
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` of
`VladimirReshetnikov/ProveIt`.

This review was conducted by a separate agent from the construction author.
It is an internal AI-assisted mathematical review, not external peer review
or a proof-assistant certificate. The literal emitted packets require the
separate algebraic audit described at the end.

## Source and proposed change

The source is package 64's `integer41/quartic41.json`, with the full
source34 fixed coefficient tuple. Its mathematical source argument is
`integer41/PROOF41.md` together with `PROOF44.md`. The proof retains the
inherited ordinary strong-rank and signed auxiliary-index theorems. The
four coefficient ports remain jointly bound to the same source34 tuple;
the coefficient radix exponent is the odd integer 1064921.

Replace the old supplied integer coordinates by

    J_old = 3 J + 1,
    w_scale_old = 3 w + 1,

and delete the residual `X - 2 u^2` and its private coordinate `u`.
All other source rows are retained after these affine substitutions. Write

    q = beta J_old + 1,
    w_source = 4 w_scale_old,
    X = q w_source,
    Y = (2 v + 1) q^3.

Because beta = 2^1064921 - 1 is 1 modulo 3, the retained lift forces
`q = 2 (mod 3)`, `w_source = 1 (mod 3)`, hence `X = 2 (mod 3)`.
Neither q nor w_source can be zero. These congruences are restrictions on
the retained coordinates, not a consequence of an assumed square root.

## Preliminary packing and magnitude bounds

The two retained common-sign guards for F alpha and F C, where
`C = q - F - alpha`, imply that F, alpha, C have one nonzero common sign.
They imply `Q = |q| >= beta - 1 >= 16`. The packing argument of source64
PROOF44, Section 3, does not use a sign of X, eta, zeta, or Y and gives

    Q (Q^2 - 1) < R < Q^4 - 2.

The retained eta zeta guard implies that eta and zeta have the same
nonzero sign. Put

    U = |X|, Z = |Y|, xi = sign(X), delta = sign(Y),
    K = |eta + zeta|, sigma = sign(eta + zeta).

Then `U >= 4Q`, `Z >= Q^3`, `K >= 2`, and
`|E| = U Z >= 4Q^4 > 3R + 1`.
The affine w_scale replacement preserves this bound because its absolute
value is at least one. No positive-square hypothesis is being used here.

For `c = (eta + zeta)Y + eta`, set `c0 = |c|`. Since
`0 < |eta| < K`, direct examination of both signs of Y gives

    K (Z - 1) < c0 < K (Z + 1),
    sign(c) = sigma delta.

In particular c is nonzero. With `A = (X+1)Y + 2`, set

    B = |A| = (U + xi) Z + 2 xi delta,
    P = |2 X Y^2 + 1| = 2 U Z^2 + xi.

The expression for B is valid in all four signs of X and Y because
`(U-1)Z > 2`. The bounds

    B >= (U-1)Z - 2 > R,
    P > B >= 2,

follow from U >= 4Q, Z >= Q^3, Q >= 16. Thus Delta = B^2 - 1 > 0.

## The first Pell classification for both signs of X

For X positive, the first norm has discriminant
`U Z^2 (U Z^2 + 1)`; for X negative it has discriminant
`U Z^2 (U Z^2 - 1)`. In either case the first positive integer unit is
`(P,2)`. Indeed ordinate one would require an integer square strictly
between consecutive squares, while ordinate two gives P explicitly.
Consequently the two retained Pell norm equations classify as

    K = 2 psi_P(n), n >= 1,
    c0 = psi_B(p), p >= 1.

Monotonicity in parameter and index gives p > n: otherwise
`c0 <= psi_B(n) <= psi_P(n) = K/2`, contradicting `c0 > K`.

Because `P = xi (mod |E|)`, the Pell recurrence gives

    psi_P(n) = n xi^(n-1) (mod |E|).

Combining this with the retained index residual yields

    sigma xi^(n-1) 2n = R + 1 (mod |E|).

The sign on the left is either plus or minus. In the plus case,
`2n = R + 1 + t |E|` with t >= 0, so n >= (R+1)/2. In the minus case,
`2n >= |E| - R - 1 > 2R`, so n > R. Both branches therefore give a
large first index, and hence p >= 6 before any strong-rank lemma is used.

## Correct use of the inherited ordinary rank and auxiliary theorem

From p >= 6 and B >= 2,

    c0 = psi_B(p) >= (2B-1)^(p-1) > B(B^2-1)^2.

Also c0 > 2p by Pell growth and c0 > 2R because p >= 2 and B > R.
The retained ordinary strong equation is exactly

    (i c^2)^2 = Delta (f^2 - 1), i = 2r + 1.

Thus its multiplier is nonzero, c is nonzero, and every size hypothesis
of the inherited ordinary strong-rank theorem is established. That
theorem supplies a positive m with

    |f| = chi_B(m), p | m, c0 | m, m > 2p.

The retained two exposed auxiliary congruences are

    V = o f - c, V = j c - R.

The auxiliary norm has square coefficient `(i c^2)^2`. Therefore the
signed auxiliary step-down argument applies to |f| and c0. Its first
congruence can be squared, so the sign of c causes no change. It yields
`p = R`, since `0 < p,R < c0/2`. In particular, the minus branch of the
previous paragraph is impossible. In the plus branch, n < p = R and
the no-wrap interval force

    2n = R + 1.

Hence R is odd. This proof does not use the sign of X, Y, eta, zeta, q,
f, D, V, or the omitted square-root coordinate prematurely.

## Uniform ratio estimate and the root orientation

Put r = n - 1, so R = 2r + 1 and r >= 2. Standard Pell growth gives

    c0 / K >= (1/2) [ (2B-1)^2 / (2P) ]^r.

The worst simultaneous bounds B >= (U-1)Z - 2 and
P <= 2UZ^2 + 1 give

    [2((U-1)Z-2)-1]^2 - 2(2UZ^2+1)(U-3)
      = 4(U+1)Z^2 - 20(U-1)Z + 31 - 2U > 0.

The last inequality holds already for U >= 64 and Z >= 6: its value at
Z=6 is positive and its derivative in Z is positive from there onward.
Therefore

    Z + 1 > c0/K > (U-3)^r/2,

which implies `Z > 2^R` for U >= 64 and r >= 2. The last implication can
be checked using U-3 >= 16 and
`16^r/2 > 2^(2r+1)+1` for r >= 2.

Let `e = sign(c)`. At odd R, `psi_A(R) = psi_B(R)` even when A is
negative, so `c = e psi_A(R)`. Write `D = lambda chi_A(R)` with
lambda in {1,-1}. With `a = A-2` and `H = 4a+3`, the polynomial Pell
identities modulo the odd integer H are

    chi_A(R) - a psi_A(R) = 2^R (mod H),
    chi_A(R) + a psi_A(R) = 2^(-R) (mod H).

These hold for negative A and H as well. The defining root congruence
is `D - ac = X (mod H)`.

If lambda = -e, this gives `X 2^R = -e (mod H)`. But

    1 < U 2^R < U Z < |H|-1,

so `X 2^R + e` is a nonzero integer of absolute value below |H|, a
contradiction. If lambda = e, then `X = e 2^R (mod H)`. The bound

    |X-e2^R| <= U+2^R < U+Z < |H|

forces exact equality `X = e 2^R`. The comparisons with |H| follow
from `|H| >= 4(U-1)Z - 3` and U >= 64.

Finally X = 2 (mod 3) and odd R imply e = 1, since positive 2^R is
2 modulo 3 and negative 2^R is 1 modulo 3. Thus X = 2^R > 0, and
the deleted source64 square guard can be restored by the integer

    u = 2^((R-1)/2).

All retained source64 rows now vanish, so its already proved source
theorem applies. No new direct signed native compiler theorem is needed.

## Completeness of the affine restrictions

The source34 canonical witnesses have q = 2^t with t odd, R odd,
R > t, and w_source = 2^(R-t). The old J satisfies
`beta J_old + 1 = 2^t`. Reducing modulo 3, with beta = 1 and
2^t = 2 modulo 3, gives J_old = 1 modulo 3. Also R-t is positive
even, so at least two. Hence

    w_scale_old = 2^(R-t-2) = 1 (mod 3).

Both affine inverses are therefore integers. Since the new variables are
unrestricted integers, their possible zero or negative values are allowed.
Deleting the square guard needs no additional witness. This establishes
the reverse existence implication.

## Conclusion and remaining literal audit

The new semantic reduction is mathematically coherent, conditional on
exactly the same inherited ordinary rank, signed auxiliary, native
coefficient adapter, and K215/refutation theorems as source64. It neither
assumes consistency nor proves it. The arguments use integer arithmetic,
finite Pell recurrences, and the source's named theorems and can be
formalized in ZFC. This review does not export a derivation in the
repository's object-language ZFC calculus.

The literal packet audit must still verify the affine substitutions, the
deleted coordinate/row, the count 40 unrestricted integer coordinates and
25 quadratic residuals, the unchanged whole source34 binding, the exact
quartic degree certificate, and any emitted monic-elimination companions.
## Completed independent literal audit

The emitted `quartic40_direct.json`, `quartic40.json`, `sextic34.json`,
and `octic29.json` were
subsequently inspected and checked by `independent_literal_audit.py`.
This checker implements its own sparse integer-polynomial ring using
variable-name monomials and an AST reader; it does not import the
construction's builder or its arithmetic implementation. It uses only
Python's standard library. Both normal and `python3 -O` executions passed.

The audit verifies all 25 retained source rows against the affine Q41
restriction, checks that the deleted row is exactly `X-2u^2`, and verifies
the exact new variable list. For each companion it substitutes the full
restoration into all 25 quartic rows. Precisely six rows vanish identically
for the sextic and eleven for the octic; every other row agrees exactly
with the corresponding delivered companion row. There are no unaccounted
conditions or rational restorations.

The resulting independently computed metrics are:

| Packet | Integer unknowns | Residuals | Exact SOS degree | Symbolic monomials |
|---|---:|---:|---:|---:|
| Direct-coordinate quartic | 40 | 25 | 4 | 393 |
| Affine-J,w quartic | 40 | 25 | 4 | 614 |
| Sextic | 34 | 19 | 6 | 614 |
| Octic | 29 | 14 | 8 | 1238 |

Symbolic monomials here retain the four fixed ports as separate formal
indeterminates; they are not the count after collecting actual numerical
coefficients. All listed unknowns and all four ports are live. The exact
coefficients are `[tau^4] Q40=1`, `[r^2 c^4] Q34=4`, and
`[a^4 f^4] Q29=1`, each independently recovered by exact expansion.
These certificates survive the authentic fixed-coefficient specialization.

The audit decompresses and authenticates all four native payloads against
the retained source34 manifest, checks their bit lengths and raw sizes,
and verifies the actual inequalities needed in the packing proof. In
particular beta is exactly `2^1064921-1` and is 1 modulo 3. The numerical
tuple occupies 532,479 raw bytes. It also checks the signed ratio identity
by exact polynomial arithmetic. The machine-readable receipt is
`certificates/INDEPENDENT_LITERAL_AUDIT.json`.

The full final `PROOF.md` was read after generation and agrees with the
sign-uniform argument reviewed above. No mathematical or transcription
defect was found in this independent review. The inherited unbounded
theorems and the absence of a new proof-assistant certificate remain the
explicit scope boundaries.

## Final direct-coordinate quartic audit

The additional primary packet `quartic40_direct.json` was independently
audited after the companion packets. It makes precisely the substitution
`X_old = 3 X3 - 1` in every retained source64 row, deletes only row 22
(`X_old - 2u^2`), and deletes only its private coordinate `u`. Original
coordinates `J` and `w_scale` are retained. The independent checker
compares all 25 literal residuals to this exact source substitution,
compares the full ordered coordinate list, checks the source packet hash,
and verifies equality of the complete coefficient binding with the
affine-J,w packet. No coefficient or source-calibration change accompanies
this refinement.

Independent expansion finds exactly 393 symbolic SOS monomials, compared
with 388 in the 41-variable source parent. All 25 residuals have exact
degree two; all 40 declared unknowns and all four coefficient ports are
live. The coefficient of `tau^4` is exactly 1, so the quartic degree
survives specialization to the authenticated native integer tuple. Both
normal and optimized executions of the extended independent checker
passed; the receipt includes this fourth packet and the parent metrics.

I also checked the changes to the unbounded proof in `PROOF.md`, section
9. The direct residue forces `X = 2 (mod 3)`, hence `X != 0`. At a zero,
the retained source relation is still `X = 4 q w_scale`; therefore
`w_scale != 0` and `|X| >= 4|q|`. This is exactly the only lower-bound
consequence previously supplied by the affine restriction on `w_scale`.
The packing bounds require no residue restriction on `J`. Thus all signed
Pell and growth steps reviewed above apply unchanged and recover
`X = e 2^R` with odd `R` and `e` in `{1,-1}`. Since `2^R = 2 (mod 3)`,
the imposed residue forces `e = 1`, restoring the deleted square witness
`u = 2^((R-1)/2)`.

For completeness, a canonical parent zero has `X_old = 2^R` with odd
`R`; the integer `X3 = (2^R + 1)/3` supplies the required direct coordinate.
All remaining parent coordinates are retained. This direction requires
no further congruences on `J`, `w_scale`, or the coefficient radix. The
direct-coordinate refinement is therefore covered by the same consistency
equivalence. The 34- and 29-variable companions remain projections of the
affine-J,w packet, as their reconstruction uses its monic `X` coordinate.
No unproved division-by-three reconstruction is used for those companions.
