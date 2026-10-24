# Independent audit: scalar saturation and centered four-root norm

## Verdict

PASS for the new ordinary arithmetic transformation, with the inherited
native/compiler and syntactic-refutation calibration kept explicitly conditional
on the same pinned source. No new proof-assistant endpoint, proof of consistency,
global minimum, or smaller variable-count record is established by this audit.

The audited candidate is `norm/equation.json`:
12 unrestricted integer variables, 141 live binary arithmetic operations,
exact degree 768. Its 149-operation cancellation-aware companion `norm/equation_reduced.json` is exactly the
same polynomial, not merely an equation with the same zero existence.

The essential mathematical changes are I = r c^2, S = s r H,
K_red = X(2X - 3c) - 2, A_c = Phi_H(HT + K_red), and the integral shear
n_old = n + QV. The auxiliary radicand is S^2 delta Cy, not a rational
function. The six fixed coefficient ports are unchanged.

## 1. Quantifiers, bootstrap, and signs

The proof must not infer c != 0 from S != 0. The new scale has no factor c.
The correct order is:

1. H is odd and nonzero on every raw assignment; Delta > 1.
2. delta = Delta^2 I^2 - 1 is never zero, including at I = 0.
3. If S = 0, the norm equals A_c^16. This is nonzero because
   A_c = H^5 pi(T + K_red/H), and pi(x) = (x^2+3)(x^3-19) has no rational zero.
4. Thus s and r are nonzero. Divide a vanishing conjugate factor by S.
5. Prime separation works before assuming I != 0. Its squared 3-adic orders
   are 0, 2, 4, and 6+v_3(Dg), with a zero guard term deleted. At I = 0,
   delta = Cy = -1, so the auxiliary root is still a 3-adic unit.
6. All roots are rational. In particular Dg is an integer square, so Pair > 0.
   The joint positivity lemma gives G > 0 and eta*zeta > 0.
7. If c = 0, eta*zeta = -Y(Y+1)k^2 <= 0. Hence c != 0, I != 0, and Q > 1.
8. Only now use the adjacent-coefficient Pell descent to prove that the
   auxiliary root divided by delta is integral.

The joint guard implication is sign-safe: if ab - (t^2-a-b+1)^2 > 0,
then ab > 0; both a and b negative would make the squared term at least
(|a|+|b|+1)^2 > ab, a contradiction. Hence both are positive.

All signs of a, c, I, V, X, Y, and H remain unrestricted. The integral
factor gives S | A_c and therefore H | K_red^5. This alone does not imply
H | K_red. For example, 243 divides 3^5 but does not divide 3.

## 2. The fifth-power saturation argument is valid

The exact identity, checked symbolically, is

    2 K = K_red + H c X,
    K = X(X + 2ac) - 1,
    H = 4a + 3.

Since H is odd, H | K_red^5 implies H | K^5. The inherited signed
pre-projection argument, which does not require a main-root congruence,
gives R = 2r0+1 with r0 >= 24, c = sigma psi_(a+2)(R), and

    m > (x-3)^r0/2 - 1,
    x = |X|, m = |Y|, sigma = sign(c).

The authentic fixed beta gives a uniform raw-input bound, not merely a
canonical-witness bound: |6j+1| >= 1, |q| >= beta-1, and
|12w+4| >= 4. Thus x >= 4(beta-1) > 2^64 for every integer j,w.

The exact signed Pell congruence is

    2^R K = Pi modulo H,
    Pi = (sigma X - 2^R)(2^R sigma X + 1).

Taking fifth powers proves H | Pi^5. No prime factor of H is removed,
no nonunit is cancelled, and no orientation has yet been imposed.

For u = 2^R, each factor in Pi has absolute value less than 2u x, so

    |Pi|^5 < 2^(10R+10) x^10 = 2^(20r0+20) x^10.

Also |H| >= 4(x-1)m-3 > x(x-3)^r0: the remaining difference is
(x-2)(x-3)^r0 - 4x + 1, positive already for x >= 64 and r0 >= 1.
Therefore

    |H| > x^(r0+1)/2^r0.

At x >= 2^64, r0 >= 24, the exponent gap is

    64(r0-9) - (21r0+20) = 43r0-596 >= 436 > 0.

Consequently |Pi|^5 < |H|. Integer divisibility forces Pi = 0, and its
odd second factor is nonzero. This gives sigma X = 2^R and restores the
same integral main root and gamma as the pinned signed source.

## 3. Full supported-modulus interpolation

Fix the canonical data A0 even, R = 3 mod 4, c = psi_A0(R), c = R mod 4,
and the chosen positive guard witness s. Choose one strong pair

    I = psi_A0(m0), f = chi_A0(m0), 4 s c^2 | I,

with m0 positive and even. The pair is fixed before choosing any requested
residue. Retain the parent's proved bound v_p(m0) <= v_p(I) for p | I and
period lambda = 4m0 f modulo f^2. Put

    rho = Delta I, D = rho^2 - 1, d = lcm(lambda, 4I).

Since gcd(f,I) = 1, v_p(d) = v_p(4I) for every p | I. The old interpolation
lemma supplies one index nu0 = 3 mod 4 and an integral T0. For h >= 0 set

    nu(h) = nu0 + d h,
    T(h) = [chi_rho(nu(h))/rho + c - f^2(c-R)]/(4I f^2).

This is integral. The period lambda preserves the numerator modulo f^2;
the congruence chi_rho(nu)/rho = -nu mod 4rho^2 for nu = 3 mod 4
preserves it modulo 4I. These coprime divisibilities give the full denominator.

### Independent proof of the lifting calculation

Write chi = chi_rho and psi = psi_rho. For a multiple d0 of 4,

    psi(4) = 4rho(2rho^2-1),
    chi(4)-1 = 8rho^2(rho^2-1).

For odd p | rho, let a = chi(4), b = psi(4). Then p | b and a = 1 mod p.
In the second coordinate of (a+b sqrt(D))^k, for k prime to p the first
binomial term k a^(k-1)b has valuation v_p(b), while all remaining odd
terms have larger valuation. For k = p the first term has valuation
v_p(b)+1. Middle binomial coefficients are divisible by p, and the final
b^p term has valuation p v_p(b) > v_p(b)+1, also for p=3. Iterating p
and the prime-to-p case gives

    v_p(psi(d0)/rho) = v_p(d0).

For p = 2, rho is even. Odd multiples preserve the second-coordinate
valuation by the same first-term argument. Every doubling adds exactly one,
because psi(2k) = 2 chi(k) psi(k) and chi(k) is odd. Starting at index 4
gives exactly the same displayed valuation.

For odd p, chi(d0)+1 is a unit and the norm identity gives

    v_p(chi(d0)-1) = 2(v_p(rho)+v_p(d0)).

For p=2, chi(d0)=1 mod 8, so v_2(chi(d0)+1)=1, giving

    v_2(chi(d0)-1) = 2(v_2(rho)+v_2(d0))-1.

Now, for odd nu, psi(nu) and D are p-units whenever p | rho. Pell addition
expresses the change in V_nu = chi(nu)/rho as

    V_(nu+d0)-V_nu
      = V_nu(chi(d0)-1) + psi(nu) D psi(d0)/rho.

The second term has valuation exactly v_p(d0), and the first has strictly
larger valuation. Hence, with d0=d(h1-h2),

    v_p(T(h1)-T(h2)) = v_p(h1-h2),  p | I.

Thus T(h) induces an injection, and hence a permutation, on every ring
Z/p^e Z with p | I. CRT gives every class modulo every M whose prime
support is contained in I. This is stronger than the old linear congruence
modulo 4rho^2 and does not incorrectly extrapolate that congruence.

In the new construction r = I/c^2 and M = sr. Since 4s c^2 | I, every
prime of M divides I, even if M does not divide I. Therefore the theorem
applies with this fixed pair and this already determined M.

## 4. Completeness and the precise zero-set claim

Choose the native outer witness, then t, then s, then the strong pair I,f
and r=I/c^2. The canonical main projection gives integer kappa=K_red/H.
Select an intersective root a mod M=sr of pi(a+kappa), then interpolate
T=a mod M with the same fixed I,f. Therefore

    A_c/S = H^4 pi(T+kappa)/(sr)

is integral. Choose the final n using the signed integral roots and subtract
QV for the centered equation. There is no positivity restriction on n and
no hidden division by a possibly zero integer.

The shear n_old=n+QV is an actual bijection of integer assignments because
QV is an integer polynomial in the other eleven variables. It therefore
preserves integer zero sets exactly under that bijection. The broader
scalar/scale replacement establishes equivalence of integer-zero existence,
not pointwise equality or a claimed bijection with every source zero.

The doubled-auxiliary centered alternative also preserves zero existence:
its root is 2 delta y and completeness can choose the corresponding new n.
It is not literally the same polynomial as the undoubled auxiliary equation,
and doubling must not be described as just the n shear. This alternative
is not needed for the final degree-768 packet.

## 5. Exact norm identity, live counts, and degree

The independent checker does not import a builder. It constructs

    F4(y;a,b) = y^4 - 2(a+b)y^2 + (a-b)^2,
    F16(Z;a,b,e,d) = resultant_y(F4(y;a,b), F4(Z-y;e,d)).

The resultant has 495 terms. Expanding the literal DAG tail at its named
radicand and center cutpoints gives exactly that polynomial. The changed
prefix blocks, reduced K, scale, carrier, and shift are checked separately
as exact symbolic identities; the first 83 literal nodes are identical to
the pinned parent's prefix.

For degree, put B=Sn-A_c and L=SQV. The auxiliary radicand is L^2-E, where

    E = S^2[Q(V^2+1)-1].

The exact paired norm is a product of eight factors

    (B+L-alpha)^2-(L^2-E)
      = B^2 + 2LB + E + alpha^2 - 2(B+L)alpha,

where alpha is one of the eight signed sums of the three other roots.
The degrees are

    deg(B)=35, deg(L)=61, deg(E)=92,
    deg(a)=34, deg(b)=50, deg(e)=62.

Thus 2LB has degree 96. Every competing term has degree at most 92,
except B^2, of degree 70, and none can cancel this unique top term.
The product therefore has degree 8*96=768 and leading form (2L_top B_top)^8.
The equivalent reduced DAG independently has syntactic bound 768.

Let q0=6 beta j, W00=12w and

    a0 = 2 q0^4 W00 v = 2^7 3^5 beta^4 j^4 w v,
    R0 = -q0^3(W00 C-q0 z).

Then

    B_top = -4^5 a0^5 T^5,
    L_top = -4 s r^5 c^8 a0^7 R0,
    (2L_top B_top)^8 = 2^104 s^8 r^40 c^64 a0^96 R0^8 T^40.

Selecting the z term in every R0 factor gives the actual coefficient

    [j^416 w^96 v^96 z^8 s^8 r^40 c^64 T^40] P
       = 2^808 3^512 beta^416 > 0.

Its exponents sum to 768. No values of the other five fixed ports can
cancel this coefficient, and authentic beta is positive.

## 7. Reproducible checks and limitations

Run `python audit_independent.py` or `python -O audit_independent.py`.
All checks use explicit exceptions rather than disableable assertions.
The receipt validates all six authentic coefficient payloads against pinned raw SHA256 values, bit lengths, and minimal byte lengths, including the already-shifted MF convention. The diagnostic substitutions use all six authentic values, not dummy coefficient replacements. It also records source SHA256 values, live counts, exact resultant and
block equalities, two finite-field univariate degree diagnostics, 210 exact
integer valuation diagnostics, and fixed-pair residue permutations modulo
8, 27, and 125. The latter includes powers exceeding their exponents in I.

Negative controls alter I, the scale, K, the norm constant, output arithmetic,
and declared counts; all are rejected. A step-2 example rejects the
unjustified removal of the 4-divisibility condition in the lifting argument.
Finite tests do not prove the universal interpolation theorem or substitute
for the unbounded saturation proof above. No full Diophantine zero is sought.

The authoritative literal files, coefficient payloads, and checker were copied into a temporary ZIP, re-extracted into a clean directory, and checked normally and under `python -O` without builder imports or original-workspace paths. See `CLEAN_REPLAY.json`. Python 3 and SymPy are the only runtime requirements.
