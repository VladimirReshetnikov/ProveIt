# A 48-operation conditional test for native positive ternary digits

The conditional base-three Pell component admits a five-operation outer
mask in place of six. Together with its unchanged 43-operation kernel,
this gives 48 operations: 29 multiplications and 19 additions/subtractions,
with seventeen positive Pell unknowns and eleven equations.

The digit alphabet changes from {0,1} to {1,2}. This is a conditional
component theorem. Construction and bounds of the packed word, a compatible
local computation, input and output interfaces, and parity enforcement are
not included in its 48 operations. No smaller universal bound is claimed.

## 1. Native positive-digit mask

Let N>=1, L=3^N, and 0<=P0<L. Put

    D0=3L, r=3P0+2.                                  (1)

Then

    D0 divides binom(2r,r)
      if and only if each of the N ternary digits of P0 is 1 or 2. (2)

Leading positions up to N are included: an omitted leading digit is zero
and fails the test. In all cases the three-adic valuation is at most N+1;
it equals N+1 exactly for the accepted words.

The number-theoretic input is the standard carry form of Kummer's theorem,
as stated in [Granville's binomial-coefficient introduction](https://dms.umontreal.ca/~andrew/Binomial/intro.html).
The particular native-digit mask is derived here.

Indeed, the ternary digits of r are the initial digit 2 followed by the
N digits e_0,...,e_(N-1) of P0. In doubling r, the initial digit produces
a carry. With an incoming carry, an interior position produces another
carry exactly when 2e_i+1>=3, that is, e_i>=1. Kummer's carry theorem gives
at most N+1 carries, one at each of these positions. The incoming carry
beyond the highest position is at most one and cannot generate another
carry there. Maximal valuation is therefore equivalent to all N digits
being positive. A missing carry cannot be compensated at another position.

Because 3 is odd, (1) gives r=P0 modulo 2. The even-P0 hypothesis used in
the current positive half-parameter converse is retained explicitly.

## 2. Conditional input and exact arithmetic

Supply integers q,P0 satisfying

    q>=3, q^3<=P0<q^4.                               (3)

These bounds are hypotheses of this component, not free comparisons in
its arithmetic schedule. Construct

    q2=q*q,
    L=q2*q2,
    D0=3*L,
    pP=3*P0,
    r_rhs=pP+2,

and use the free equality r=r_rhs. These are four multiplications and
one addition. In particular neither a repunit nor a subtraction from
D0 is needed.

The retained 43 primitives are exactly those in
`EXPLORATION_BASE_THREE_PELL_KERNEL.md`. For completeness, abbreviate

    U=wD0, Y=sD0, E=UY, Q=UY^2, P=2Q+1,
    a=Y(U+1), A=a+3, M=6a+8, D=A^2-1=a^2+M,
    J=2r+1, R=ic^2, K=R^2, u=J+jc.

The seventeen supplied positive unknowns are

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

In addition to r=r_rhs, the ten kernel equalities are

    tau(tau+1)=(E^2+U)(Yk)^2,
    c=Yk+eta, k=eta+zeta,
    k=r+1+hE,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+Dc^2,
    R^2=D(f^2-1),
    K(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                           (4)

The complete checker is
`../verification/explore_base_three_positive_kernel.py`. It has an explicit
48-instruction schedule and fresh source polynomials using D0=3q^4 and
r=3P0+2. All eleven source comparisons are checked, including the same
acyclic penultimate adjustment

    ((ic^2)^2-D(f^2-1))*(u^2-y_aux^2).

The scale D0=3q^4 is not assumed to be a square. In fact, after q is a
power of three, its three-adic exponent is odd, so it is not a square.
The proof below uses the actual inequalities in (3), not an unproved
integer square root or an inherited square-scale hypothesis.

## 3. All preliminary bounds before decoding

Equations (1) and (3) give

    D0>=243,
    3q^3+2<=r<D0, r>=83,
    D0<r^2.                                          (5)

For the last inequality, r>3q^3 implies r^2>9q^6>3q^4=D0.
Consequently arbitrary positive kernel witnesses satisfy

    U,Y>=D0,
    E>=D0^2>r+1,
    a>=D0(D0+1)>J.                                   (6)

The proof in Sections 2-3 of the 49-operation base-three note applies
with these inequalities. Its only changed numeric index threshold is
p>=r+2>=85 in place of p>=100. To make clear that this is sufficient,
the first norm gives k=psi_P(t), and P=1 modulo E yields

    t=r+1+zE, z>=0.

The main norm gives c=psi_A(p), d=chi_A(p). Since P>A and c>Yk>k,
we have p>t, hence p>=85. The usual lower Pell bound gives

    c> A^6 > A(A^2-1)^2=AD^2,
    c>Y(r+1)>J, 0<2p<=c.

These are all the hypotheses of the generic relaxed auxiliary rank
lemma and the half-parameter main-index recovery. That argument is
independent of the scale being square and yields

    p=J, c=psi_A(J), d=chi_A(J).

If z>=1, E>r and

    (2P-1)-4A=4Y(U(Y-1)-1)-11>0

give c/k<1/2, contradicting c/k>Y. Thus t=r+1 exactly. Neither
prime-power decoding nor parity has been used to obtain these indices.

## 4. Ratio, exponent and central-binomial decoding

Set xi=(U+1)^(2r)/U^r. The same ordinary Pell estimates at these exact
indices give

    c/k > xi*(1+5/(2a))^(2r)*(1+1/(2Q))^(-r) > xi,
    c/k < xi*(1+3/a)^(2r).

The strict lower factor follows from 10Q>a. For the upper factor,
(5)-(6) give

    6r/a < 6/(D0+1) <= 6/244 < 1/2.

The elementary binomial bound therefore gives

    c/k < xi*(1+12r/a).

The positive interval Y<c/k<Y+1 now implies xi<Y+1 and hence

    Y>=U^r, a>U^(r+1),
    0<c/k-xi<24r/(U+1).                              (7)

For T_j=chi_A(j)+(3-A)psi_A(j), the recurrence proof in Section 5
of the base-three note gives T_j=3^j modulo M=6a+8. The exponent
equation in (4) thus gives U=3^J modulo M. Both sides lie in (0,M):

    U<a<M,
    3^J=3*9^r<U^(r+1)<a<M,

using U>=243. Hence U=3^J exactly. Since D0=3q^4 divides U,
q is a power of three.

After this exponent conclusion, U>48r and the error in (7) is less
than 1/2. The exact binomial-symmetry tail estimate is

    xi=F+T, F an integer,
    0<T<4^r/(2U)=(1/6)(4/9)^r<1/6,
    F=binom(2r,r) modulo U.

The interval and strict lower ratio force Y=F exactly, by the same
integrality argument as in the 49-operation proof. Since D0 divides
both Y and U,

    D0 divides binom(2r,r).

Now L=q^4 is a power of three. The mask theorem (2) proves that every
ternary digit of P0, including its leading positions below L, is 1 or 2.
This proves the soundness implication from (3)-(4), without any parity
hypothesis on the supplied input.

## 5. All-positive converse

Suppose q>=3 is a power of three, every ternary digit of P0 below q^4
is 1 or 2, and P0 is even. Such a word automatically satisfies the lower
bound in (3), because

    P0 >= (q^4-1)/2 > q^3.

The strict inequality holds for q>=3. The mask theorem gives the
required central-binomial divisibility. Define r by (1); it is even,
so J=1 modulo 4. Choose

    U=3^J, w=U/D0,
    Y=floor((U+1)^(2r)/U^r), s=Y/D0,
    a=Y(U+1), A=a+3, D=A^2-1, E=UY, P=2UY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1).

Both U,D0 are powers of three and D0<r^2<3^(2r+1), so w is a
positive integer. The exact binomial expansion, central-binomial
divisibility and D0|U make s a positive integer. Therefore the
preliminary estimates used above apply to these choices too. They give

    Y<xi<c/k<Y+2/3,

so eta=c-Yk and zeta=k-eta are positive integers. Set

    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E,
    gamma=(d-U-ac)/M.

The odd parameter P, Pell index congruence, and elementary exponent
recurrence make these integers; strict growth makes tau,h positive.
For gamma, d-ac=3c-psi_A(J-1)>2c>U proves positivity.

Finally choose the relaxed and half-parameter witnesses at this A,c,J:

    m=2cJ, f=chi_A(m), i=D*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

The integer divisibility c^2|psi_A(m), the odd-index polynomial,
and its two positive-sign congruences for J=1 modulo 4 are exactly
those proved in Section 7 of the base-three kernel note. They make
all displayed quotients integral. The bound
u>(2R-1)^(J-1)>(2A)^(J-1)>c>J makes o,j positive. The Pell norm
at R gives the last norm in (4). Thus every supplied Pell unknown
is a positive integer. No complete auxiliary tuple is numerically
materialized by the regression.

## 6. Interface consequences and verification scope

Four positive supplied fields packed in base q as
P0=F0+qF1+q^2F2+q^3F3 automatically give P0>=q^3 before any power
decoding, provided their standard upper bounds make P0<q^4. If field
boundaries are ternary-aligned after decoding, (2) gives native positive
digits in each field. Alignment and upper bounds are separate compiler
obligations; they are not inferred merely from four positive values.

When four such fields satisfy an equality of the form F0+F3=F1+F2,
their total sum is even. Since q is odd after power decoding, their
Horner packing is then even as well. This is a possible zero-additional-
operation source of the positive-converse parity hypothesis if that
equality already belongs to a future local verifier. It is not asserted
for arbitrary four fields.

The exact checker records every primitive and all fresh source residuals.
Its finite regression separately checks all ternary words of lengths
one through ten against independent factorial valuations, preliminary
bounds at non-power q values as well as powers, six even native inputs
with q=3,9,27, and exact canonical ratio cases at r=83,84. The latter
cases are standalone kernel estimates, not claims that both indices
come from accepted mask inputs. These finite checks support the general
proof; they do not establish a computation, input, or halting interface.

The subsequent `EXPLORATION_NATIVE_TERNARY_OVERFLOW.md` proves a larger
preliminary range and supplies the missing shared packing bound in a
complete 60-operation four-field relation. Its application in
`EXPLORATION_NATIVE_TERNARY_RIPPLE.md` gives complete bounded increment
and borrow relations in 63 operations. The original conditional count
and its proof above are retained unchanged.
