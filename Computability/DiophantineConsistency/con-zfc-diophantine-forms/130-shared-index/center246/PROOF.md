# A weighted polynomial center of degree 246

This companion gives a new explicit ten-positive-variable equation, at
121 binary arithmetic operations and exact total degree 246. It changes
the fused radical's weight and its polynomial center. The arithmetic
kernel and the whole original compact44 coefficient tuple are retained
from `candidates/ten-positive-gap-fusion` at ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.

The ordinary proof below composes with exactly the parent's inherited
source61/native/controller/refutation calibration. It does not provide a
new Lean, Rocq, or internal object-ZFC certificate, and it does not assert
Con(ZFC). The result is an improvement in degree within the ten-positive
family, at the cost of more operations. No global simplicity minimum is
claimed.

## 1. Complete equation

The ten independent inputs `J,F,alpha,i,T,x,Y,n,eta,zeta` are strictly
positive integers. The four fixed ports `beta,K0,MC,MF` are exactly the
whole original compact44 tuple in `coefficients/`. Their hashes and bit
lengths are in `coefficients/BINDING.json`; they satisfy

    beta odd, beta >= 31, K0 > 0, 0 < MC < beta < MF < 2 beta.

Define the following integer polynomials:

    q = beta J + 1,     X = q + x,        C_d = q - F - alpha,
    g = q(q-1),         B = (q K0 + X) C_d - q F,
    mu = q^2 + 1,       t = mu Y,         L = X + 1,
    A = t L + 1,        Delta = A^2 - 1,  H = 4 A - 5,
    k = eta + zeta,     c = k Y + eta,
    v = X t^2,          D = 1 + v(v+1)k^2,        E = i c^2,
    R = [(q-1)(q-F)+alpha](q^2-1) + (MC+q MF)J,
    e = k - R - 1,
    Fs = 1 + Delta D E^2,       Q = Delta^2 D E^2,     delta = Q - 1,
    b = c(T+alpha) - R,         V = Fs b - c,
    Dnum = Q V^2 - 1,
    P = q^4(q-1),              M = P mu^2 H,
    Kpos = X(3c-2X)+2,         W = 1 + g b.

The new formulas are

    Q1 = k^2 [t^3 L^2 X^2 - t^2 L X^2
              + t(L^3-2L+1) - L^2 + 2],
    Q3 = k^2 [t X^2 - 3L + 6],
    lambda = 8 L^3,
    Gamma = E [8 L^3 A D - 4 Q1 - Q3],
    a = lambda^2 D Fs.

Finally set

    Z = P mu^2 [H(n+V+Gamma-bB)+Kpos]
        + H[mu^2(gY-q^3 B-(q-1)X)-P e],
    N = (delta Z^2 - M^2 Dnum - delta M^2 a)^2
        - 4 delta M^4 a Dnum.

The equation is `N = 0`. All displayed symbols are polynomial
abbreviations, not additional unknowns. `equation.json` contains the full
121-row binary arithmetic schedule, with precisely these ten witnesses
and four fixed ports. Its operations are 73 multiplications, 25 additions,
and 23 subtractions. Multiplication by a fixed integer counts as one
operation; reuse and leaves are free.

The exact rational carrier, used only in the proof, is

    Z/M = n + V + Gamma + Kpos/H + Y/q^3
          - W B/g - X/q^4 - e/mu^2.                 (1)

There is no division in the actual equation.

## 2. Why this center is a polynomial

Here regard `L,t,k` as independent and put

    A = Lt+1,
    D = 1 + k^2[(L-1)^2 t^4 + (L-1)t^2].

Direct polynomial division gives

    L^3 D = A Q1 + r1,
    r1 = L^3 + k^2(L^2-t-2),                         (2)

and `Q3` is the polynomial quotient of `L^3 D` by `A^3`, with
leading monomial `(Lt)^3`. The latter identity is

    L^3 D = A^3 Q3 + r3,

    r3 = k^2 [ L^4 t^2 + 5 L^3 t^2 - 3 L^2 t^3
              -12 L^2 t^2 + 8 L^2 t - 3 L t^2
              -16 L t + 3 L - t - 6 ] + L^3.       (3)

Thus the center uses the polynomial portions of the first terms

    L^3 D sqrt(A^2-1)
      = L^3 D A - L^3 D/(2A) - L^3 D/(8A^3) - ...

only as a discovery guide. Equations (2)--(3), and all conclusions below,
are exact polynomial identities. No convergence or asymptotic estimate is
used to justify the equation. The factor 8 clears the two fixed rational
coefficients. The variable factor `L^3` permits polynomial cancellation
in both correction terms.

The paid circuit uses a shorter exact expression for the correction.
Writing `p=A-1` and `u=tX^2`,

    4 Q1 + Q3
      = k^2 {u[4p(p-1)+4L+9]+4(tX-L^2)-3L+14}.     (4)

Every coefficient of (2)--(4) and of the 52-term center defect is checked
in an exact sparse rational polynomial ring by `build_verify.py`.

## 3. Uniform positive bounds for the center

On the full input domain, `L >= 33`, `t >= 1025`, and `A=tL+1`.
In fact the following estimates use only `L >= 3`, `t >= 4`.

First, `Q1,Q3` are positive. For `Q1/k^2`, write

    t^2 L (L-1)^2(tL-1)
      + t(L^3-2L+1)-L^2+2.

The first term is positive, while the second is at least
`L^3-L^2-2L+3 > 0`. Also

    Q3/k^2 >= (L-1)^2-3L+6
              = (L-2)(L-3)+1 > 0.

We have `Q1 > k^2(t+2)`: its first positive term is at least `24t^3`,
before multiplication by `k^2`, and `24t^3 > t+2` for `t >= 1`.
By (2), `r1 > -k^2(t+2) > -Q1`, so

    L^3 D > (A-1)Q1 > Q1.

Furthermore `Q3 < k^2 t X^2 < D <= L^3 D`. Consequently

    0 < 4Q1+Q3 < 5L^3 D < 8L^3 A D,

which proves the unconditional bounds

    0 < Gamma < lambda A D E.                      (5)

The useful majorization is

    lambda A = 8L^3(tL+1) <= 16tL^4 < t^4 L^4
             < Delta^2,                           (6)

since `t^3 > 16`. As `E >= 1`, (5)--(6) imply

    0 < Gamma < Q.                                (7)

These inequalities hold before any property of a zero is used.

## 4. Root extraction and the unchanged early arithmetic

The old kernel is unchanged. In particular `D > 1`, `Fs > c+1`, `Q > 1`
and `M > 0` hold on the positive domain. Since `b` is integral, either
`b=0` and `V=-c`, or `|V| >= Fs-c > 1`; hence `Dnum/delta > 0`.

The two radicands `a=lambda^2 D Fs` and `Dnum/delta` are unequal.
If equal, `delta lambda^2 D Fs = QV^2-1`, impossible modulo `D` because
`D` divides `Q` and the right side is `-1` modulo `D`.

For a zero, write `z=Z/M`. The quartic norm gives

    (z^2-a-Dnum/delta)^2 = 4a Dnum/delta.

The unequal-radicand obstruction implies `z != 0`. Therefore

    a = [(z^2+a-Dnum/delta)/(2z)]^2

is a rational square. As `lambda` is a positive integer, `D Fs` is also
a rational square, hence an integer square. Since `Fs = 1 (mod D)`,
`gcd(D,Fs)=1`, so

    D = tau^2,       Fs = f^2

for positive integers `tau,f`. Put `I=tau E`. Then

    f^2-Delta I^2=1,   Q=(Delta I)^2,   c^2 divides I.

The unchanged adjacent-Pell descent proves that the remaining rational
root `y = sqrt(Dnum/delta)` is a positive integer. The signed carrier is

    Z/M = epsilon lambda tau f + nu y,
    epsilon,nu in {1,-1}.                          (8)

Thus exactly the parent's three Pell conditions have been recovered.
None of the preceding arguments needs the sign of `B` or `Z`.

The parent's kernel analysis (copied in `source/parent_proof.md`,
sections 2--3) now applies without alteration. Its folding and
first-index lemmas imply

    c=psi_A(p), p odd and p>=3,
    c>kY>=k>=4(2v+1)>8X mu^2 Y^2,
    R<c alpha/4,
    b>c, V>0, Kpos>0.

Its auxiliary-index argument excludes the first and third auxiliary
indices and gives

    V>8Q^2,       b>8Q,
    0<y-V<b/4,    e/mu^2<b/4.                     (9)

The integer center and integer radical weight do not enter these steps.
Also `f<A I`, so (6) gives

    lambda tau f < lambda A D E < Q.

Since `Delta^2 > X` and `Q >= Delta^2`, we have `X/q^4 < Q`.
Together with (9),

    lambda tau f + X/q^4 < 2Q < b/4.              (10)

## 5. Transport soundness and source reconstruction

Solving (1) and (8) for `n` gives

    n = epsilon lambda tau f - Gamma + nu y - V
        - Kpos/H - Y/q^3 + W B/g + X/q^4 + e/mu^2.

By (7), (9), and (10), and the positivity of `Kpos/H` and `Y/q^3`,

    n < 3b/4 + W B/g.

If `B <= -1`, then `W B/g <= -W/g = -b-1/g`, giving `n < 0`,
contradicting the positive domain. Hence `B >= 0`, and `C_d > 0`.

Every later step in the parent's soundness proof is unchanged.
The new carrier is integral by (8). `Gamma` is an integer polynomial,
and `lambda tau f` is an integer, so these changes add no rational
denominators. The normalized fractional terms (1), the congruence
`W=1 (mod g)`, and the Pell kernel are exactly the old ones.
Consequently the same ordered rank argument gives `p=R`, parity makes
`q` even, the coprime projection isolates `mu^2 | e`, and the first-index
congruence and whole-product height argument force `X=2^R`.
The remaining fractions give `q^3 | Y` and the native transport
congruence. Fixed-minus parity and fresh unscaled source reconstruction
then yield a finite syntactic refutation, through the same pinned
source61/native/controller calibration as the parent.

In particular, the new construction does not replace a source theorem
with a numerical test or assume that one can cancel a nonunit modulo
the main height modulus.

## 6. Completeness with a positive carrier coordinate

Given a finite refutation, use the parent's fresh canonical witnesses
for all inputs other than `n`. Its construction supplies integral

    t0=B/g >= 0,     rho=e/mu^2 >= 1,
    sY=Y/q^3 > 0,   kappa=Kpos/H > 0,
    u=y-V > 2Q,     X/q^4 > 0,

with `sY<Y<c`, `kappa<c`, and the same positive strong/auxiliary
Pell witnesses. Set

    n = W t0 + rho + lambda tau f - Gamma
        + u - sY - kappa + X/q^4.                 (11)

Every term is an integer. From (7), `u>2Q`, and `Q>2c`,

    n > u-Gamma-sY-kappa > 2Q-Q-2c > 0.

The inequality `Q>2c` follows already from `E=i c^2`, `c>=3`, and
`Q=Delta^2 D E^2>c^4`. Substitution of (11) in (1) makes the center
equal to `lambda tau f+y`, so a factor of the norm vanishes.

This is a fresh positive existence construction. No positive pointwise
inverse from every zero of the old equation is asserted.

Sections 4--6 establish that this new polynomial has a zero in ten
strictly positive integers exactly when the parent's syntactic refutation
calculus does. Composing with the same inherited calibration gives,
by ordinary mathematics formalizable in ZFC,

    ZFC proves [ no positive integer zero of N <-> Con(ZFC) ].

## 7. Exact degree, including the competing leading term

All ten inputs have degree one and the fixed ports degree zero. The old
direct kernel has

    deg q=1, deg t=3, deg L=1, deg A=4, deg Delta=8,
    deg D=16, deg E=5, deg Fs=34, deg Q=deg delta=42,
    deg b=4, deg V=38, deg M=13.

The new weight and center have degrees `3` and `28`; `deg a=56`.
The exact center defect

    C = Gamma^2-a

has degree 34, with homogeneous leading part

    C0 = -112 L0^5 t0^5 k0^4 E0^2.                (12)

This can be derived from (2)--(3) by expansion. The included
`center_defect.json` records every one of its 52 coefficients in the
independent polynomial variables `L,t,k,E`, with weights `1,3,1,5`.
The standard-library checker reconstructs all coefficients, not merely
the degree or a numerical sample.

Write `Z=M(V+Gamma)+Z0`. The unchanged remainder has degree at most 19.
Its leading part is `Z00=-M0 b0 B0`. Set

    Theta = delta M^2 C - M^2(V^2-1)
            +2delta M(V+Gamma)Z0 + delta Z0^2.

The exact norm identity is

    N = 4delta^2 M^4 V^2 C + 4delta M^2 V Gamma Theta
        + Theta^2 - 4delta M^4 a V^2 + 4delta M^4 a. (13)

Here `deg Theta=112`, with leading part `2delta0 M0 V0 Z00`.
The degrees of the five terms in (13) are respectively at most
`246,246,224,226,150`. Therefore `deg N <= 246`.
The second term really competes at degree 246; ignoring it would not
be a valid exact-degree proof.

To prove noncancellation, use

    q0=beta J, X0=q0+x, t0=q0^2 Y, k0=eta+zeta,
    E0=i k0^2 Y^2, D0=X0^2 t0^4 k0^2,
    A0=t0 X0, Delta0=A0^2,
    delta0=Delta0^2 D0 E0^2,
    b0=-q0^3(q0-F), V0=Delta0 D0 E0^2 b0,
    M0=4q0^9 A0,
    B0=(q0 K0+X0)(q0-F-alpha)-q0 F,
    Gamma0=8X0^6 t0^5 k0^2 E0.

The complete leading polynomial is

    N0 = 4delta0^2 M0^4 V0^2(C0-2Gamma0 b0 B0).    (14)

Its first summand has degree ten in `i`; its second has degree nine.
The first summand is exactly

    -7*2^14 q0^116 X0^29 i^10 Y^57 k0^32(q0-F)^2.

It follows that the actual fixed-port polynomial has the nonzero
coefficient

    [J^116 x^29 i^10 Y^57 eta^32 F^2] N
       = -7*2^14 beta^116 != 0.                    (15)

The monomial in (15) has total degree 246. Thus the degree is exactly
246 for the full coherent coefficient tuple, with no generic-port
qualification.

## 8. Verification, provenance, and comparison

Run `python3 build_verify.py`. It uses only Python's standard library.
It rebuilds the literal graph, checks all nodes and all live inputs,
checks the complete coefficient tuple and its port box, proves the
local center identities by exact coefficient cancellation, and compares
the graph to a separately written complete formula at 72 modular inputs.
Three full rays, over primes `2^61-1`, `2^89-1`, and `2^127-1`, have
degree 246 and the leading coefficient predicted by (14). These last
finite checks are transcription controls; the unbounded equivalence
is the proof in sections 3--6, and the exact degree is proved in section 7.

The current packet records 151 successful checks. Its input graph is the
94-operation, degree-262 direct uncentered gap-fusion graph. The sharp
center in the same source gives 97 operations and degree 254. The new
weighted center gives 121 operations and degree 246, so this is a
degree/operation tradeoff, not simultaneous domination.

Polynomial parts of radical expansions already appear elsewhere in the
repository, for example `87-direct-centered-round12/norm/PROOF.md` for
a different unrestricted-integer construction. This packet claims a new
concrete application to the fused ten-positive kernel and a new verified
degree/cost point relative to the inspected frozen snapshot. It does not
claim invention of polynomial square-root expansion or worldwide priority.

The inherited proof boundaries are retained in `source/parent_proof.md`.
All four supplied coefficients belong to the whole original compact44
tuple; no BFS or other source coefficient is substituted into it.
