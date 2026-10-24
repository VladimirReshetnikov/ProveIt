# Twelve integer variables with fixed-prime separation

## Status and inherited endpoint

This note proves an arithmetic replacement of the five-root compression in
`ConZFC_Twelve_Integer_Interpolation_2026-10-24.zip`, inspected at ProveIt
commit `85ae4070019efd66ea3e58e9a67d287528094e8b`.
It uses the same coherent six fixed coefficients, the same twelve integer
coordinates, and the same generalized signed native kernel. The inherited
unbounded Pell interpolation theorem and native/compiler/K215 consistency
calibration are ordinary mathematical proofs. No new proof-assistant
certificate or internal object-ZFC derivation is asserted here.

The resulting literal polynomial has degree 2400 and 215 live binary
arithmetic operations. An integral-radicand companion has degree 2912 and
209 operations. The prior twelve-integer forms had degree 4832 with 248
operations, and degree 16000 with 223 operations. These are improvements
at twelve unrestricted integer variables, not a variable-count record:
the repository already contains ten-integer equations of higher degree.

## 1. Polynomial definitions

The independent integer coordinates are

    j, C, z, h, r, v, w, T, c, n, t, s.

Use the inherited six fixed constants `beta,K0,MC,MF,cone_A,cone_B`,
including `beta=2^1064921-1`, the already-shifted `MF`, and the determinant
scales `cone_A=2^1113`, `cone_B=2^666104`. Define

    J=6j+1, q=beta J+1, W0=12w+4,
    X=qW0, Y=(2v+1)q^3, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W0)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+qMF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    P=G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg=(3P-4)s^2+1,
    I=s r c^2, Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1,
    Dt=1+XY^2(XY^2+1)k^2,
    Dm=1+Delta c^2, b0=X+ac,
    u=HT-b0.

The shorter carrier in this contribution is

    pi(x)=(x^2+3)(x^3-19).

Its homogeneous form is

    Phi_H(z)=z^5+3H^2 z^3-19H^3 z^2-57H^5.

In the quadratic algebra `d^2=Dm`, compute `A+B*d=Phi_H(u+d)` by

    Q0=u^2+Dm+3H^2,
    C0=u(u^2+3Dm)-19H^3,
    C1=3u^2+Dm,
    A=Q0 C0+2u Dm C1,
    B=Q0 C1+2u C0,
    S=I H^5, Z=S n-A.

Let the ordinary universal polynomial

    F32(Z;A0,A1,A2,A3,A4)
      = product over all five independent signs of
          (Z - eps0 sqrt(A0) - ... - eps4 sqrt(A4)).

Every radical has even exponent after multiplying the conjugate factors,
so this is in `Z[Z,A0,A1,A2,A3,A4]`. The principal literal polynomial is

    E12 = delta^16 F32(Z;
                      B^2 Dm, 9S^2 Df, 81S^2 Dt, 729S^2 Dg,
                      S^2 Cy/delta).

This is a polynomial, not a rational expression: `F32` has degree at most
16 in each radicand, and `norm5.py:cleared_norm5` supplies a division-free
arithmetic circuit for the displayed denominator clearing. The code uses
only integer leaves, independent variable leaves, fixed coefficient leaves,
and binary addition, subtraction and multiplication.

The integral-radicand companion is

    E12_integral = F32(Z;
                      B^2 Dm, 9S^2 Df, 81S^2 Dt, 729S^2 Dg,
                      S^2 delta Cy).

## 2. A short intersective carrier

The polynomial `pi` has a zero modulo every positive integer and no zero
in any real extension of Q of degree at most two.

The second assertion follows because `x^2+3` has no real root and
`x^3-19` is irreducible by Eisenstein's criterion at 19. If the cubic had
a root in a quadratic field, its degree three minimal polynomial would
divide an extension of degree at most two, which is impossible.

For intersectivity, first let p be an odd prime other than 3 and 19. If
`x^3-19` has a root modulo p, it is simple. Otherwise it is irreducible,
and Frobenius permutes its three roots as a three-cycle, an even
permutation. Therefore the Vandermonde product is fixed and lies in F_p,
so the cubic discriminant `-27*19^2` is a nonzero square modulo p. It
follows that `-3` is a square modulo p, and `x^2+3` has a simple root.
Either root lifts to every p-power by elementary Hensel lifting.

At p=19, the root 4 of `x^2+3` is simple because `4^2+3=19` and
`2*4` is nonzero modulo 19. At p=2, the cubic root 1 modulo 2 is simple.
At p=3, write `x=1+3t`; then `x^3=19` is exactly

    t+3t^2+3t^3=2.

The polynomial on the left minus two has the simple root `t=2 mod3`,
since its derivative is 1 modulo 3. Its 3-adic lift gives a cubic root
modulo every power of 3. The Chinese remainder theorem completes the
proof for every positive modulus.

The older quintic's monotonicity is no longer needed. Here the odd
coefficient B is nonzero for an arithmetic reason, established below.
No historical-priority claim is made for the intersective quintic itself. This is the n=19 case of the classical family studied by A. M. Hyde, P. D. Lee and B. K. Spearman, "Polynomials (x^3-n)(x^2+3) Solvable Modulo Any Integer", American Mathematical Monthly 121(4) (2014), pp.355-358, DOI 10.4169/amer.math.monthly.121.04.355.

## 3. Prime-order separation lemma

Let `r_i` be finitely many nonzero algebraic square roots of rational
numbers. Suppose each subset of at least two roots has one root whose
squared p-adic valuation is the unique minimum and is even. Then no
signed nonempty subset sum is zero. Consequently, if a signed sum of all
the roots is rational, every root is rational.

Here is a purely algebraic proof of noncancellation. Divide the roots by
the rational p-power at the unique minimum, so one squared root is a
unit of `Z_(p)` and all other squared roots lie in `p Z_(p)`. Take the
product of the expressions consisting of that distinguished root minus
all signed sums of the other roots. For a subset of size at least two,
sign invariance and even parity put this product in `Z_(p)`. Modulo p it
is a power of the distinguished unit square, and is therefore nonzero.
A vanishing signed subset sum would make one of its factors zero, a
contradiction. A nonzero singleton cannot sum to zero either.

For the rationality assertion, work in the finite multiquadratic field
generated by the roots. Apply an arbitrary Q-automorphism to the rational
sum and subtract. Every root changed by the automorphism contributes
twice that root, with a sign. Noncancellation implies that no root changes.
The fixed field of all automorphisms is Q, proving the assertion. The
lemma does not require nonnegative radicands or independence of their
square classes.

## 4. Bootstrap and exact 3-adic orders

Since beta is 1 modulo 3, identically

    q=-1, W0=1, X=-1, a=H=Delta=0 (mod3).

Hence

    Dm=Df=Dt=1, Q=0, delta=-1, Cy=-1 (mod3),
    u=1, Q0=2, C0=C1=1, B=1 (mod3).

In particular delta and B are nonzero, and H is nonzero because
`H=4a+3` for integer a. The inherited affine restrictions also imply
`|q|>=beta-1>=16`, `|X|>=64`, `|Y|>=4096`, and
`|a|>=63*4096`, so `Delta>1` and `Dm>=1` unconditionally.

If `S=0`, then `I=0`. Every scaled radicand except `B^2 Dm` vanishes,
and `delta=-1`. Both principal and integral polynomials specialize to

    (A^2-B^2 Dm)^16.

The factors `A +/- B sqrt(Dm)=Phi_H(u +/- sqrt(Dm))` are nonzero: their
arguments divided by nonzero H lie in a real extension of degree at most
two, where pi has no zero. Therefore no polynomial zero has S=0. It
follows that I,s,r,c are all nonzero.

At a zero, divide a vanishing conjugate factor by S. In the rational
variant, the five normalized radical terms are

    B sqrt(Dm)/S, sqrt(Cy/delta), 3sqrt(Df),
    9sqrt(Dt), 27sqrt(Dg).

The first four squared 3-adic orders are respectively

    -2v3(S), 0, 2, 4,

and `v3(S)>=5` because `3|H` and I is an integer. If Dg is nonzero,
the last squared order is `6+v3(Dg)>=6`, possibly odd. If Dg is zero,
omit its term. Every subset with at least two terms thus has a unique
even minimum. The separation lemma proves all five roots rational.
The same calculation holds for the integral auxiliary radicand
`delta Cy`, which is also a 3-adic unit.

Rational roots of the integer radicands are integers. In particular,
`Dg=g^2>=0`. Because s is a nonzero integer, `P<=0` would force
`Dg=(3P-4)s^2+1<=-3`. Thus P>0. The inherited joint positivity lemma
then yields `G>0` and `eta*zeta>0`.

## 5. Integral auxiliary root and restored main congruence

For the rational variant, write the auxiliary root as y in Q. It obeys

    Q V^2-(Q-1)y^2=1.

Here `Q=(Delta I)^2>1`. The adjacent-coefficient Pell descent proves y
integral. Explicitly, after signs are removed, write `y=u/b` in lowest
terms. The norm gives `b^2|(Q-1)`, so `(Q-1)y` is integral. For V>1,
the transform

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves the norm, makes V' integral, preserves the reduced denominator
b of y because `2Q-1=1 modb`, and satisfies `-V<V'<V`. The last strict
inequalities use `y>V` and `(Q-1)y<QV`; the norm forbids V'=0. Replacing
V' and y' by their absolute values gives descent to V=1, where y=1 and
b=1. The integral-radicand companion first produces an integer root
`ytilde` of `delta Cy`; apply the same argument to `y=ytilde/delta`.

After signs are absorbed into the integer roots, the rational variant has

    S n = A+B d+S(y+3f+9tau+27g),
    d^2=Dm, f^2=Df, tau^2=Dt, g^2=Dg.

Thus `H^5 | A+B d = Phi_H(HT+d-b0)`. Monicity and p-adic comparison of
the four displayed terms of Phi force `H | HT+d-b0`: if `p^e||H` and
`v_p(HT+d-b0)=b<e`, the leading fifth power has valuation 5b, strictly
below the other three terms. It could not be divisible by `p^(5e)`.
Consequently `gamma=(d-b0)/H` is an integer. The integral variant gives
the identical conclusion, with ytilde in its root sum.

All restored equations are now exactly those in the inherited generalized
signed strong kernel:

    d=X+ac+gamma H, d^2-Delta c^2=1,
    f^2-Delta I^2=1, I=s r c^2 != 0,
    (Delta I)^2 V^2-((Delta I)^2-1)y^2=1,
    V=f^2(c-R+4IT)-c,
    tau^2-XY^2(XY^2+1)k^2=1,
    G>0, eta*zeta>0.

The previously proved signed rank, orientation, native decoding, compiler,
and K215 calibration therefore yield a finite syntactic ZFC refutation.

## 6. Completeness and the order of witness choices

Start with a canonical native witness supplied by a finite ZFC refutation.
The inherited interpolation theorem supplies the following quantifier
order. After choosing a joint-positivity witness t and a Pell positivity
witness s, choose one strong pair `I,f`, with `4s c^2|I`, such that EVERY
residue class modulo I can be attained by an integer T satisfying the
auxiliary Pell equation. Set `r=I/(s c^2)`.

The same fixed I works for all requested residue classes. This is stronger
than the assertion that the auxiliary Pell equation has infinitely many
solutions; it is proved in the inherited archive by a squared-modulus
period and a Lucas valuation calculation. The period is `4*m*f`, not
`4*m`, and this distinction is retained.

Choose a root a of `pi(x+gamma)` modulo I, possible by Section 2, then
choose the interpolated T with `T=a modI` and its integer auxiliary root
y. The canonical main root d obeys

    A+B d = H^5 pi(T+gamma),

which is divisible by `S=I H^5`. Finally set

    n=(A+B d)/S+y+3f+9tau+27g.

This is an integer and makes one conjugate factor zero. For the integral
companion replace y in this formula by `delta*y`. This proves both
directions of the new arithmetic equivalence, using no consistency or
halting assumption. Composing the ordinary calibration gives the desired
ZFC-provable equivalence between absence of integer zeros and Con(ZFC).

## 7. Exact degree and operation counts

The relevant degrees are

    deg S=34, deg A=35, deg B=28,
    deg Dm=14, deg Df=20, deg Dt=34, deg Dg=46,
    deg Q=deg delta=32, deg V=25, deg Cy=82.

In the cleared norm, `cn=S^2 Cy` has degree 150. Every competing cleared
term has smaller degree: `delta Z^2` has degree 102 and the four cleared
integer radicands have degrees 102,120,134,146. Therefore `cn^16` is the
unique contribution of degree 2400. Write

    q0=6 beta j, W00=12w,
    a0=2 q0^4 W00 v=2^7*3^5*beta^4*j^4*w*v,
    I0=s r c^2,
    R0=-q0^3(W00 C-q0 z), b=4I0 T-R0.

The leading form is exactly

    2^320 a0^288 I0^128 b^32.

Its monomial `j^1152 w^288 v^288 s^160 r^160 c^320 T^32` has nonzero
coefficient `2^2400*3^1440*beta^1152`. The exponents sum to 2400. The
coefficient does not involve any other fixed coefficient port, so it
remains nonzero for the actual inherited tuple.

For the integral companion, the unique highest radicand is
`S^2 delta Cy` of degree 182. Its sixteenth power yields degree 2912
with leading form `2^320 a0^352 I0^160 b^32`. The monomial
`j^1408 w^352 v^352 s^192 r^192 c^384 T^32` has coefficient
`2^2848*3^1760*beta^1408`.

The literal graph census charges binary addition, subtraction and
multiplication, including multiplication by fixed scalars and squaring.
Reused registers and fixed numeral leaves are free. The principal graph
has 44 additions,139 multiplications,32 subtractions:215 operations.
The integral companion has 44 additions,133 multiplications,32
subtractions:209 operations. Every declared coordinate and coefficient
leaf is live. These counts concern the delivered circuits only, without
claiming optimal arithmetic circuit complexity.
