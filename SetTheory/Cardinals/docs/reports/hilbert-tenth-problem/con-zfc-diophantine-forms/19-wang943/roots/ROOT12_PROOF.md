# Four-root amalgamation: twelve positive unknowns

## Result and scope

Two new explicit integer polynomials use twelve strictly positive supplied
unknowns. The primary `root12_product.json` has degree 1545 and a fully
charged 140-operation circuit (94 multiplications, 46 additions/subtractions).
The alternative `root12_scaled_y_product.json` has degree 1625 and the same
140-operation ledger. Both replace the thirteen-positive-variable frontier
by twelve variables, at a substantial degree/circuit-cost increase. Neither
is claimed globally minimal.

This is ordinary mathematics relative to the same four-port arithmetic
interface and literal K215/Pell calibration as package 09-combined13 at
commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`. The selected default is
now the independently audited complete compact Wang943 tuple with
B=2^(5^10), not the old T-shape coefficients. Its recipe is
`../compiler/WANG943_COMPACT_LAYOUT.md`, and exact file hashes, aliases and
proof links are specified in `COEFFICIENT_BINDING.json`. The circuit aliases
are beta=beta, K0=K, MC=MC, MF=MF_source. All four ports are replaced
together; MF_source is the shifted mask, never MF_native. The original
pinned T-shape tuple remains a documented derivation fallback only.

The complete Wang943 compiler audit establishes the same native-window,
mask-population, positive-gap and signed-domain interface hypotheses used
below. Changing that full coefficient backend does not change a supplied
variable, arithmetic gate or degree. This is not a new end-to-end Lean/Rocq
formalization. The positive-solvability statement is the same blank-machine
halting condition; its unsolvability therefore has the inherited Con(ZFC)
equivalence.

The generated three-equation systems have 136 charged operations
(92 multiplications, 44 additions/subtractions), residual degrees
(7,2,1536) or (7,2,1616), respectively.

## 1. Retained expressions and the four roots

Retain the upstream definitions

    q=(B-1)J+1, Cword=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    Lfirst=E*kY, A1=1+Lfirst*(Lfirst+k), A2=1+Delta*c^2,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-hE-R,
    Nt=(K0+w)*Cword+q-F-z*(q-1), B0=X+a*c.

The primary construction supplies

    J,F,alpha,z,h,j,T,s,w,eta,zeta,t > 0,

and defines i=Hj. The alternative supplies i instead of j and does not
restrict i further. In either case define

    I=i*c^2, S=Delta*I, Q=S^2, D=1+I*S, d=Q-1,
    v=c*T, b=c+R*D,
    e=Q*(D*v^2+b^2)-1, Baux=2*Q*v*b.

The roots to recover are

    tau^2=A1, g^2=A2, f^2=D,
    d*y^2=e-Baux*f=Q*(v*f-b)^2-1.

The omitted main quotient will be gamma=(g-B0)/H. Its sign is not assumed.

For the product construction the integer unit factors will initially allow
Nk=Nt=epsilon with epsilon in {+1,-1}. The source's weak transport bootstrap,
including Cword=0, gives q>=16, Cword>=0, 0<R<E-2 and k>R. In particular
b,v,Baux,d are positive. These facts are established before any eliminated
root is used.

## 2. Conjugate bounds and economical weights

Since Delta>1 and I>1,

    D=1+Delta*I^2 < Delta^2*I^2=S^2.

Every algebraic conjugate f' has |f'|=sqrt(D)<S. For any real conjugate y'
of a restored auxiliary root,

    |y'|^2 = [Q*(v*f'-b)^2-1]/d
             < 2*(S*v+b)^2.

Thus the positive integer Ybound=2*(S*v+b) bounds |y'| strictly.

Choose Wbound=Ybound in the primary construction, and Wbound=d*Ybound in
the alternative. Define

    Pweight=H*Wbound, K=Pweight+1, M=6*Wbound,
    u=6*Pweight=H*M, Z=H*t+K*B0.

Here gcd(K,H)=1. The primitive element is t=K*gamma+M*tau+y in the
primary construction, or t=K*gamma+M*tau+r with r=d*y in the alternative.

The weights need not contain A2. Indeed a+2<2E and c<2kY, so

    A2 < 16*A1.

Also Pweight>=14, hence

    u*sqrt(A1) > K*sqrt(A2)+H*Wbound,
    K*sqrt(A2) > H*Wbound.

For the first inequality, subtract K*sqrt(A2)<4K*sqrt(A1); the remainder
exceeds (2*Pweight-4)*sqrt(A1)>Pweight=H*Wbound. These inequalities
separate opposite tau conjugates first, and opposite g conjugates second.

## 3. An explicit polynomial, not a generic-resultant assertion

In the free rank-four algebra over Z with generators r0,s0 satisfying
r0^2=A1 and s0^2=A2, put

    W=Z-u*r0-K*s0.

For the primary construction set

    F(r0,s0)=[d*W^2-H^2*e]^2-H^4*Baux^2*D.

For the alternative set

    F(r0,s0)=[W^2-H^2*d*e]^2-H^4*d^2*Baux^2*D.

In either case define the explicit integer polynomial

    Res12 = product over sigma,tau in {+1,-1} of F(sigma*r0,tau*s0).

The product is invariant under both sign changes and lies in Z[A1,A2,
all other registers]. The JSON files give every binary arithmetic gate of
an expanded rank-four norm evaluator, without radicals or quantified
registers. Thus this definition is constructive even when A1 or A2 is a
square or the two quadratic extensions coincide.

The three-equation system is Nk=Nt=1, Res12=0. The single polynomial is

    P12=Nk*Nt*(1+Res12)-1.

## 4. No spurious irrational branches

At a zero of Res12, one of the four factors vanishes after choosing real
roots tau^2=A1 and g^2=A2. In the primary case put

    y=(Z-u*tau-K*g)/H,
    f=(H^2*e-d*(Z-u*tau-K*g)^2)/(H^2*Baux).

Then f^2=D and d*y^2=e-Baux*f. All denominators displayed here are
nonzero by the weak bootstrap. In the alternative put

    r=(Z-u*tau-K*g)/H,
    f=(H^2*d*e-(Z-u*tau-K*g)^2)/(H^2*d*Baux), y=r/d.

Then f^2=D and r^2=d*(e-Baux*f).

Take a normal closure of the number field generated by these roots. Under
each automorphism, tau and g go to their positive or negative real square
roots, and the linear relation makes every image of y (or r) real. The
bounds of section 2 therefore apply to every conjugate, not only the
initially chosen branch. If an automorphism changed tau's sign, the change
of u*tau would exceed in absolute value all possible changes of K*g and
H*y (or H*r), contradicting the fixed rational value Z. Thus every
automorphism fixes tau. The second inequality similarly shows that every
automorphism fixes g. Consequently tau,g and then y (or r) are rational.
The auxiliary identity gives rational f. Since tau^2, g^2 and f^2 are
integers, tau,g,f are integers.

This establishes rationality globally, including coincident/square
quadratic fields. No discriminant-nonzero or generic-primitive-element
assumption is used.

### 4a. Primary denominator recovery

Here i=Hj, so Q is divisible by H and gcd(H,d)=1. Write rational y in
lowest terms. Since d*y^2 is an integer, its denominator squared divides
d. The denominator of gamma=(g-B0)/H divides H. The equality

    t-M*tau=K*gamma+y

has integer left side and summands with coprime denominators, so both
summands are integers. Hence y is an integer, and K*gamma integer together
with gcd(K,H)=1 proves gamma integer.

### 4b. Alternative denominator recovery

Since r^2=d*(e-Baux*f) is an integer and r is rational, r is an integer.
Then K*gamma=t-M*tau-r is an integer, and gcd(K,H)=1 again proves gamma
integer. Finally y=r/d is rational and V=v*f-b is an integer satisfying

    S^2*V^2-(S^2-1)*y^2=1.

The rational auxiliary saturation lemma in section 5 makes y an integer.
This route imposes no restriction on the original positive i.

## 5. Rational auxiliary Pell saturation

If S>=2 and V are integers, and rational y satisfies

    S^2*V^2-(S^2-1)*y^2=1,

then y is an integer. Factor S^2-1=d0*b0^2 with squarefree d0>1.
The rational number b0*y is an integer: if reduced denominator n>1
existed, n^2 would divide squarefree d0. Both

    (S,b0), (|S*V|,|b0*y|)

are positive integral Pell solutions for d0, so they are powers m,n of a
common least positive integer-coefficient Pell unit. Write its first and
second coordinates as chi_j,psi_j. Since chi_m=S divides chi_n=|S*V|,
reduce n modulo 2m using chi_(j+2m)=-chi_j modulo chi_m, and then reflect
the remainder into 0<=r<=m. If r<m, 1<=chi_r<chi_m, impossible. Thus
n is an odd multiple of m. The standard addition formula (or geometric
series factorization of the Pell unit) gives psi_m|psi_n. As psi_m=b0,
the quotient |y|=psi_n/psi_m is an integer.

This proof does not require d0=S^2-1 to be squarefree initially.

## 6. Restored signs and the inherited compiler

The recovered f,tau,y,g and gamma need not initially be positive. None is
silently made positive inside an affine defining expression. Replace tau
and y by their absolute values; their equations are unchanged. If f<0,
replace f,T simultaneously by -f,-T. All relevant formulas depend on
these coordinates through f^2 and T*f. The result has f>0 but possibly
signed T, signed gamma, and possibly signed main root g.

The signed-domain proof already audited in round2 supplies the exact
extension needed here. In outline, the first/main Pell equations classify
k=2*psi_P(n), c=psi_(a+2)(p), |g|=chi_(a+2)(p). Strong rank from
f^2-Delta*(ic^2)^2=1 and the two auxiliary congruences V=-c mod f and
V=-R mod c give R=plus-or-minus p mod c. The independent bounds
0<R,p<c/2 give p=R, without using signs of T,V or g. The first-index
bound and Pell ratio force Nk=Nt=1 and recover the ordinary ratio
interval.

Before assuming a sign for g, that ratio gives a>X*2^R. If g<0, its
defining congruence g=X+ac+gamma H and the Pell projection force
H | X*2^R+1. But 0<X*2^R+1<H, a contradiction. Therefore g>0, the
projection yields X=2^R, and gamma>0 follows from
chi_(a+2)(R)-a*c=2c-psi_(a+2)(R-1)>c>X. The remaining half-binomial,
mask-population and native-window decoding do not inspect auxiliary signs.

Thus the restored tuple implies the same blank-machine halting condition.
Canonical positive auxiliary witnesses can be regenerated afterward. This
is an equivalence in existence, not a coordinate-preserving bijection.

## 7. Product guard and completeness

Baux is even. Modulo 4 the factor F is the square of its bracket, so
Res12 is congruent to the square of that bracket's rank-four norm. Hence
Res12 is a square modulo 4, and the integer unit 1+Res12 cannot be -1.
At P12=0 it is therefore +1, Res12=0, and Nk=Nt are equal units. The weak
bootstrap and signed decoding above explicitly cover these two signs.

For the alternative, start with any positive normalized upstream solution
and set t=K*gamma+M*tau+d*y>0. The corresponding F factor is zero, hence
Res12=0 and P12=0. No old witness or coefficient needs adjustment.

For the primary, regenerate the normalized strong auxiliary root so that
H divides i. Fix the already decoded main c=psi_(a+2)(R). In the finite
ring (Z/NZ)[s]/(s^2-Delta), N=H*c^2, the element (a+2)+s is a unit
(norm 1), so some positive power ell is 1. Choose m divisible by ell and
2cR. Then psi_(a+2)(m) is divisible by H*c^2. Set

    f=chi_(a+2)(m), i=psi_(a+2)(m)/c^2, j=i/H,
    S=Delta*psi_(a+2)(m),
    V=chi_S(R)/S, y=psi_S(R).

The decoded R=3 mod4 and standard odd-quotient identities give
V=-c mod f and V=-R mod c. Together with gcd(c,f)=1 and f^2=1 mod c,
these make T=(V+c+R*f^2)/(c*f) a positive integer. Thus all required
normalized auxiliary equations hold with j>0. Finally choose
t=K*gamma+M*tau+y>0.

Important correction: choosing merely m=2cRH does not establish H|i in
general. The finite-unit-period argument above is the required repair.
The period need not be encoded into the polynomial; it is only an
existence witness in completeness.

## 8. Exact degrees and supplementary checks

For the primary construction the key degrees are

    A1,A2,H,I,S,Q,D,v,b,Ybound,K,u,Z
    =22,22,6,17,29,58,46,6,50,50,56,56,67.

Let Ltop be the degree-11 leading form of Lfirst. Both A1 and A2 have
leading form Ltop^2, and B0 has leading form Ltop. Let Ktop denote the
nonzero leading form of K; u has leading form 6Ktop. The four real-root
linear factors W have leading forms

    Ktop*Ltop*(1-6*sigma-tau), sigma,tau in {+1,-1}.

Their four numerical multipliers are -6,-4,6,8, all nonzero. In the
primary construction the term H^2*e is lower-degree than d*W^2, and the
term H^4*Baux^2*D is lower-degree than its square. Therefore the leading
form of Res12 is

    1152^4 * dtop^8 * (Ktop*Ltop)^16,

of exact degree 8*58+16*(56+11)=1536. For the alternative the analogous
leading form is 1152^4*(Ktop*Ltop)^16. Here deg(K)=90, hence Res12 has
exact degree 16*(90+11)=1616. These expressions are nonzero polynomial
forms, not generic numerical claims. Multiplying the nonzero Nk and Nt
leading forms adds 7+2, yielding exact degrees 1545 and 1625.

`check_root12.py` was independently authored and does not execute received
repository programs. It checks 100 assignments per variant against a
separate four-dimensional quotient-algebra product, verifies all gate and
port liveness, checks both exact-degree diagnostics at two finite-field
specializations, and checks 21 synthetic complete radical-kernel witnesses
per variant. It also searches 49,000 rational auxiliary Pell cases as a
supplement to, not a replacement for, section 5's proof.

No accepting ZFC-recognizer run or astronomical full Pell tableau is
claimed. The finite tests check the emitted elimination circuits, not the
inherited machine calibration or Con(ZFC).
