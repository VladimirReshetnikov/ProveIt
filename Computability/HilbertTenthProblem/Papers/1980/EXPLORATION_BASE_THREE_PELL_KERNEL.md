# A conditional 43-operation power-of-three and binomial kernel

This is a component theorem, not a universal certificate or a replacement
for the finite Rule 110 history interface. It adapts the retained
43-operation Pell component to the odd-prime digit test in
`EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md`. The new component proves both
power-of-three decoding and the required three-adic divisibility. Its
positive converse is proved for even packed words. A computation
encoding that supplies the packed-word bound, the parity condition, and
faithful ternary local relations is still separate work.

Fixed numerals and equality tests are free. All 17 supplied Pell
witnesses are positive integers; arithmetic registers may be signed.
The companion exact checker is
`../verification/explore_base_three_pell_kernel.py`.

## 1. Conditional interface and equations

Let q and P0 be supplied integers satisfying

    q>=2, 0<=P0<q^4.

These inequalities are hypotheses of the component, not free tests in
its arithmetic certificate. Construct

    L=q^4, D0=9L, r=D0-3P0-1.                         (1)

The six operations constructing these values are displayed in Section 8.
The exact positive-domain implication proved below is

    the ten Pell equations have positive witnesses
      => q is a power of three and D0 | binom(2r,r).   (2)

Conversely, if q is a power of three, P0 has only ternary digits zero
and one, and P0 is even, all ten equations have positive witnesses.
The converse does not impose a parity assumption in the soundness proof.

Write, as mathematical abbreviations,

    U=wD0, Y=sD0, E=UY, Q=UY^2, P=2Q+1,
    a=Y(U+1), A=a+3, M=6a+8, D=A^2-1=a^2+M,
    J=2r+1, R=ic^2, K=R^2, u=J+jc.

Here P is a Pell parameter and P0 is the packed word. The 17 positive
witnesses are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

The ten free equality tests assert the following equations:

    tau(tau+1)=(E^2+U)(Yk)^2,
    c=Yk+eta,  k=eta+zeta,
    k=r+1+hE,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+Dc^2,
    R^2=D(f^2-1),
    K(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                            (3)

In the source polynomial of the penultimate equation, K can instead be
written D(f^2-1). The checker verifies the exact triangular correction
from the preceding equation. Equation (1), when r is a supplied
positive witness, adds one free equality test.

## 2. Bounds before any exponent or digit decoding

The integer bound P0<=q^4-1 gives

    6q^4<r<9q^4=D0,   D0>=144,   r>=98.                (4)

For proof notation only put n0=3q^2. Then D0=n0^2 and n0<r<n0^2.
In particular

    U,Y>=D0>=144,
    E>=D0^2>r+1,
    a>=D0(D0+1)>J.                                    (5)

The first norm in (3) is exactly

    (2tau+1)^2-(P^2-1)k^2=1,

because Q(Q+1)k^2=(E^2+U)(Yk)^2. Thus k=psi_P(t) at a positive
index t. Since P=1 modulo E, the integer Pell polynomials give
psi_P(t)=t modulo E. The first-index equation in (3) and (5) imply

    t=r+1+vE, v>=0.                                   (6)

The main norm gives c=psi_A(p), d=chi_A(p), for some positive p.
Moreover

    P-A=UY(2Y-1)-Y-2>0.

If p<=t, monotonicity of the Pell sequence in both its base and its
positive index would give c<=k, contrary to c>Yk>k. Hence

    p>=t+1>=r+2>=100,
    c>AD^2,   c>J>1,   0<2p<=c.                       (7)

For the large-coordinate inequality, the elementary bound
psi_A(p)>=(2A-1)^(p-1) gives c>A^6>AD^2. The interval supplies
c>Y(r+1)>J. These bounds use neither the relaxed auxiliary norm nor
the half-parameter norm nor the exponent equation.

## 3. Exact main and first indices

Apply the generic rank result proved in
`PELL_RELAXED_AUXILIARY_PROOF.md` to the main norm, (7), and
R^2=D(f^2-1), R=ic^2. Its hypotheses are A>1,
c=psi_A(p)>AD^2, and positive supplied coordinates. It yields

    f=chi_A(m), p|m, c|m, R=D psi_A(m)

for a positive auxiliary index m. In particular 0<2p<=c<=m.
This statement does not depend on whether A is a+2, a+3, or a+4.

The half-parameter proof in `HALF_PARAMETER_PELL_92_PROOF.md`, Sections
3--4, now applies without any change. To make the interface explicit,
the last norm in (3) is

    (Ru)^2-(R^2-1)y_aux^2=1.

Its positive index z is odd, since an even chi index is plus or minus
one modulo R, whereas R divides Ru. For z=2h0+1, the integer
polynomial chi_R(z)/R=Q_h0(R^2) satisfies

    Q_h0(1-A^2)=(-1)^h0 psi_A(z),
    Q_h0(0)=(-1)^h0 z.

Modulo f, use R^2=1-A^2 and u=c. Squaring the resulting psi
congruence gives chi_A(2z)=chi_A(2p) modulo chi_A(m). The retained
chi step-down lemma, with comparison index 2p<=m, yields
z=plus or minus p modulo m and hence modulo c. Modulo c, use
c|R and u=J+jc to obtain J=plus or minus p modulo c.
Since 0<J,p<c, either J=p or J+p=c. The latter is impossible:
c=psi_A(p)=p modulo 2, while J is odd. Therefore

    p=J, c=psi_A(J), d=chi_A(J).                        (8)

No assumption that r is even has entered this argument.

If v>=1 in (6), Pell growth and E>r give

    c/k <= (2A)^(2r)/(2P-1)^(r+E)
        <= (2A/(2P-1))^(2r)<1/2,

where the changed exact difference is

    (2P-1)-4A=4Y(U(Y-1)-1)-11>0.

This contradicts c/k>Y. We have proved, before exponent decoding,

    k=psi_P(r+1).                                      (9)

## 4. The perturbed ratio

Set xi=(U+1)^(2r)/U^r. From (8)--(9) and the ordinary upper and
lower Pell estimates,

    c/k > xi (1+5/(2a))^(2r) (1+1/(2Q))^(-r) > xi.     (10)

The last inequality follows from
(1+5/(2a))^2>1+5/a>1+1/(2Q), using 10Q>a.
For the upper estimate,

    c/k < xi (1+3/a)^(2r).

The initial bounds are sufficient here:

    6r/a<6/(D0+1)<=6/145<1/2.

The elementary binomial bound (1+t)^m<=1/(1-mt)<1+2mt, for
0<mt<1/2, therefore gives

    c/k < xi (1+12r/a).                                (11)

The positive interval says Y<c/k<Y+1. Together with (10), this
implies xi<Y+1. Since xi>U^r and Y is an integer,

    Y>=U^r, a>U^(r+1).                                 (12)

Using xi<Y+1<2Y in (11) gives

    0<c/k-xi<24r/(U+1).                                (13)

We have not yet used an upper bound on the right side of (13).

## 5. An elementary exponent congruence

The following recurrence supplies the exponent decoding directly. For
arbitrary positive integers A,b, put M_b=2Ab-b^2-1 and

    T_j=chi_A(j)+(b-A)psi_A(j).

The sequence T_j has initial values T_0=1,T_1=b and the Pell
recurrence T_(j+2)=2A T_(j+1)-T_j. Since
2Ab-1=b^2 modulo M_b, induction proves

    T_j=b^j modulo M_b.                                (14)

The induction uses multiplication and addition only and requires no
division modulo M_b. In this application b=3, A=a+3, M_b=6a+8=M>0.
Equations (8), (14), and the exponential equality in (3) give

    U=3^J modulo M.

Both sides already lie strictly between zero and M. Indeed U<a<M,
and, using U>=144 and (12),

    3^J=3*9^r<U^(r+1)<a<M.

Consequently

    U=3^J.                                             (15)

Since D0=9q^4 divides U, every prime factor of q is three. Thus q
is a power of three. This direct congruence proof avoids the stronger
cubic size bounds used by a general exponent criterion; those bounds
are unnecessary and are not assumed at the q=2 preliminary endpoint.

## 6. Exact rounding and the ternary predicate

Now U=3^(2r+1)=3*9^r>48r, so (13) is less than 1/2. Expand
xi=F+T, where

    F=sum_(j=r)^(2r) binom(2r,j) U^(j-r),
    T=sum_(j=1)^r binom(2r,r-j)/U^j.

Binomial symmetry gives the exact useful bound

    0<T<4^r/(2U)=(1/6)(4/9)^r<1/6.                    (16)

Hence F is the integer part of xi, and F=binom(2r,r) modulo U.
The interval and ratio estimates give

    F<xi<c/k<Y+1,
    Y<c/k<xi+1/2<F+2/3.

Integrality forces Y=F. As D0 divides both Y and U,

    D0 | binom(2r,r).                                  (17)

The independently proved odd-prime mask theorem, with prime three and
L=q^4, now implies that every ternary digit of P0 is zero or one.
This proves the soundness implication (2), without any input parity
assumption.

## 7. Positive converse and its parity hypothesis

Suppose q is a power of three, 0<=P0<q^4 is a ternary Boolean word,
and P0 is even. Define D0,r,J as in (1). The odd-prime mask gives
D0|binom(2r,r). Also r=P0 modulo 2, so r is even and J=1 modulo 4.

Choose

    U=3^J, w=U/D0,
    Y=F=floor((U+1)^(2r)/U^r), s=Y/D0,
    a=Y(U+1), A=a+3, D=A^2-1, E=UY, Q=UY^2, P=2Q+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1).

The quotient w is a positive integer: D0 and U are powers of three,
and D0=n0^2<r^2<3^(2r+1)=U. Formula (16), together with central
binomial divisibility and D0|U, proves that s is a positive integer.
The same estimates at these chosen indices give

    Y<xi<c/k<Y+2/3.

Thus eta=c-Yk and zeta=k-eta are positive integers. Put

    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E,
    gamma=(d-U-ac)/M.

Since P is odd, chi_P(r+1) is odd, so tau is integral and positive.
The Pell congruence modulo E proves h integral; strict Pell growth
proves h positive. Equation (14) proves gamma integral. For positivity,

    d-ac=3c-psi_A(J-1)>2c>U,

because c>=A>U and J>1. All first/main norm and interval equations
therefore have positive witnesses.

For completeness, choose the relaxed auxiliary and half-parameter
witnesses exactly at these newly chosen A,c,J:

    m=2cJ, f=chi_A(m),
    i=D psi_A(m)/c^2, R=ic^2=D psi_A(m),
    y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

The integer divisibility c^2|psi_A(m) follows by expanding the power
(d+c sqrt(D))^(2c): its square-root coefficient divided by c is
2c*d^(2c-1) modulo c. The relaxed norm follows immediately.
Odd J makes chi_R(J)/R an integer polynomial in R^2. Since J=1
modulo 4, the two polynomial congruences in Section 3 have positive
signs and give u=c modulo f and u=J modulo c. The two quotients
o,j are therefore integers. They are positive because R>=c^2>A and

    u>(2R-1)^(J-1)>(2A)^(J-1)>psi_A(J)=c>J.

The Pell norm at R verifies the last norm in (3). This supplies every
positive witness, with no materialization of these enormous auxiliary
values needed for the general proof.

The even-P0 condition is used only for this positive converse. This
note makes no assertion that every odd ternary Boolean P0 has positive
half-parameter witnesses, and does not silently replace the supplied
witness domains by nonnegative domains.

## 8. Exact cost and evidence boundary

The outer arithmetic is

    q2=q*q, L=q2*q2, D0=9*L,
    pP=3*P0, gap=D0-pP, r_rhs=gap-1.

It has four multiplications and two subtractions; compare r=r_rhs.
The 43-operation core is obtained from the retained base-two core by
changing just the two constants in M=4a+3 to M=6a+8. The existing
discriminant calculation D=a^2+M then gives (a+3)^2-1 exactly.
The core still has 25 multiplications and 18 additions/subtractions.
Combined, these are 49 operations, 29 multiplications and 20
additions/subtractions, with 11 equality tests. The bound on P0 and the
parity interface are not included in those 49 operations.

The checker expands every fresh source residual, verifies every
primitive, and records the sole triangular correction

    ((ic^2)^2-D(f^2-1))*(u^2-y_aux^2).

On the positive solutions, y_aux>1 and both u^2-y_aux^2 and
1-y_aux^2 are negative. This is permitted: intermediate integers need
not be positive, and subtraction is checked by reversed addition.

Its focused finite checks verify the exponent recurrence, exact
canonical Pell norms, both ratio inequalities, rounding, and positive
integral tau,h,gamma, including r=64 and r=98. They do not instantiate
the enormous auxiliary index m, do not constitute complete packed
system examples, and do not replace the general proof above.
Separately, twelve actual admissible mask inputs, with q=3,9,27 and
P0=0,4,10,40, check all preliminary hypotheses, parity, and the exact
three-adic central-binomial valuation. Those checks do not materialize
their Pell witnesses. The standalone r=64,98 ratio cases are not
misidentified as admissible mask inputs.

This is a conditional ternary Booleanity component. Neither a smaller
universal operation count nor a complete ternary computation encoding
is claimed.

The subsequent `EXPLORATION_BASE_THREE_POSITIVE_KERNEL.md` gives a
48-operation conditional variant for digits one or two, using a different
mask and a directly justified nonsquare scale. Its changed word bounds
and even-word converse are explicit; it does not supersede the present
zero-or-one digit predicate for unchanged packed inputs.
