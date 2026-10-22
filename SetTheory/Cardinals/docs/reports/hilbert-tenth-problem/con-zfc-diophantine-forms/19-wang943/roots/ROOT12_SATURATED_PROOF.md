# Final twelve-variable improvement: saturate the unscaled auxiliary root

## Result

`root12_saturated_product.json` is the final preferred twelve-positive-variable
construction. Its literal circuit has 139 operations, consisting of 93
multiplications and 46 additions/subtractions. Its exact total degree is 1257.
The corresponding three-equation system uses 135 operations and has residual
degrees 7,2,1248.

This improves both earlier twelve-variable variants. The older artifacts and
their proofs remain unchanged as derivation records; they are not the preferred
final result. The improvement is obtained by applying rational auxiliary Pell
saturation earlier in the proof, before recovering the main quotient gamma.
Neither a divisibility restriction i=Hj nor an auxiliary scaling r=(Q-1)y is
necessary.

All four fixed ports are the complete compact Wang943 tuple specified by
`COEFFICIENT_BINDING.json`, with B=2^(5^10) and aliases
beta=beta, K0=K, MC=MC, MF=MF_source. MF_source is the shifted mask. The
compiler transfer and literal K215 calibration have exactly the dependencies
specified in `ROOT12_PROOF.md`; this is ordinary mathematics, not a new
end-to-end proof-assistant formalization or proof of Con(ZFC).

## 1. Literal definition

The twelve supplied positive integers are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t.

Use the same retained arithmetic as `ROOT12_PROOF.md`, section 1:

    q=beta*J+1, Cword=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    L=E*kY, A1=1+L*(L+k), A2=1+Delta*c^2, B0=X+a*c,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-hE-R,
    Nt=(K0+w)*Cword+q-F-z*(q-1).

Define computed expressions, not new supplied variables,

    I=i*c^2, S=Delta*I, Q=S^2, D=1+I*S, d=Q-1,
    v=c*T, b=c+R*D,
    e=Q*(D*v^2+b^2)-1, Baux=2*Q*v*b,
    Wbound=2*(S*v+b), Pweight=H*Wbound,
    K=Pweight+1, M=6*Wbound, u=6*Pweight=H*M,
    Z=H*t+K*B0.

For formal quadratic roots r0^2=A1, s0^2=A2 put

    F(r0,s0)=[d*(Z-u*r0-K*s0)^2-H^2*e]^2-H^4*Baux^2*D,
    Res12=product over sigma,tau in {+1,-1} of F(sigma*r0,tau*s0).

The four-sign norm is an integer polynomial. The JSON gives a finite literal
rank-four norm circuit, including all constants and every binary operation.
It is valid when either square root is rational or the quadratic fields
coincide. The system and polynomial are respectively

    Nk=1, Nt=1, Res12=0,
    P12=Nk*Nt*(1+Res12)-1=0.

## 2. Product signs and the pre-root bounds

Baux is even, so F is congruent to the square of its bracket modulo 4.
Its four-sign norm Res12 is therefore a square modulo 4. At P12=0 every
integer factor is a unit. The factor 1+Res12 cannot be -1, so Res12=0
and Nk=Nt=epsilon with epsilon in {+1,-1}. The system has epsilon=1.

The retained weak transport argument gives Cword>=0, q>=16, 0<R<E-2,
and k>R for both possible signs. Consequently all of b,v,Baux,d are
strictly positive, independently of any root reconstruction.

Because Delta>1 and I>1, D<S^2. Also a+2<2E and c<2kY imply A2<16A1.
Every real conjugate f' with (f')^2=D satisfies |f'|<S. If

    d*(y')^2=Q*(v*f'-b)^2-1,

then Q/d<=2 gives |y'|<Wbound. These facts imply

    u*sqrt(A1)>K*sqrt(A2)+H*Wbound,
    K*sqrt(A2)>H*Wbound.

Indeed Pweight>=14, and the first left side minus K*sqrt(A2) is larger
than (2*Pweight-4)*sqrt(A1)>Pweight=H*Wbound. The second follows from
K=Pweight+1 and sqrt(A2)>=1.

## 3. Algebraic recovery and conjugate separation

Res12=0 gives real signs tau^2=A1 and g^2=A2 for which F(tau,g)=0.
Define

    y=(Z-u*tau-K*g)/H,
    f=(e-d*y^2)/Baux.

The vanished factor gives f^2=D, and the second definition gives

    d*y^2=e-Baux*f=Q*(v*f-b)^2-1.

In a normal closure every automorphism sends tau,g,f to their positive
or negative real square roots. The linear expression for y therefore
makes every conjugate of y real. The preceding strict bounds apply to
all of them.

If an automorphism changed tau's sign, the resulting change in u*tau
would exceed all possible changes in K*g and H*y, contradicting the
fixed rational value Z. Thus every automorphism fixes tau. Applying the
second inequality afterward shows that every automorphism fixes g.
Therefore tau,g,y and then f are rational. Since tau^2,g^2,f^2 are
integers, tau,g,f are integers.

This is an actual global rationality argument, not a generic resultant
claim or a nonvanishing assumption about an unspecified denominator.

## 4. The simplification: saturate y before recovering gamma

At this point S is an integer and

    V=v*f-b

is an integer, because f has already been proved integral. The rational y
satisfies

    S^2*V^2-(S^2-1)*y^2=1.

The rational auxiliary Pell saturation lemma proves that y is an integer.
Crucially, this lemma uses no gamma, no main-root quotient congruence and
no assertion that i is divisible by H.

For completeness, factor S^2-1=d0*b0^2 with squarefree d0>1. Rationality
and the equation imply b0*y is integral. In the fundamental integer-
coefficient Pell sequence for d0, write

    (S,b0)=(chi_m,psi_m),
    (|SV|,|b0*y|)=(chi_n,psi_n).

Since chi_m divides chi_n, reduction of n modulo 2m and the strict growth
of chi imply n is an odd multiple of m: modulo chi_m one has
chi_(j+2m)=-chi_j, and a reflected remainder 0<=r<m cannot have
chi_r=0 modulo chi_m. The Pell addition formula gives psi_m|psi_n.
Hence |y|=psi_n/psi_m is integral. The standalone independent proof is
`../audit/RATIONAL_AUXILIARY_PELL_SATURATION.md`.

Now set gamma=(g-B0)/H. The linear relation gives

    K*gamma=t-M*tau-y,

an integer. Also H*gamma=g-B0 is an integer and gcd(K,H)=1. Bezout's
identity therefore proves gamma integer. This order removes the earlier
unnecessary i=Hj restriction and the scaled auxiliary root.

## 5. Soundness and direct completeness

The restored equations are exactly the normalized first, main, strong
and auxiliary Pell equations, provisionally with signed tau,g,f,y,gamma.
The signed-domain argument in `ROOT12_PROOF.md`, section 6, applies
unchanged. It first recovers the correct index p=R and unit signs; only
then does the main projection exclude g<0 and prove gamma>0. Absolute
values of tau,y are harmless, while changing f's sign also changes T's
sign. No affine expression is incorrectly replaced by its absolute value.
The remaining mask and native-window decoder establishes the inherited
blank-machine halting condition.

Conversely, start with any positive normalized upstream witness. Retain
its original i without modifying an index or imposing a divisibility
condition. With its positive gamma,tau,y, choose

    t=K*gamma+M*tau+y>0.

Then Z-u*tau-K*g=H*y, the corresponding F factor vanishes, and therefore
Res12=0 and P12=0. This is direct completeness. No finite-period repair
or reselected auxiliary family is needed for this final variant.

## 6. Exact degrees, costs, and checks

The degrees of the main expressions are

    I,S,Q,D,b,Wbound,K,u,Z = 11,23,46,34,38,38,44,44,55.

Let Ltop be the degree-11 leading form of L. The leading forms of A1 and
A2 are both Ltop^2, and that of B0 is Ltop. Thus the four conjugate linear
forms Z-u*r0-K*s0 have leading forms

    Ktop*Ltop*(1-6*sigma-tau), sigma,tau in {+1,-1}.

Their numerical multipliers are -6,-4,6,8. The lower terms H^2*e and
H^4*Baux^2*D cannot cancel their leading contributions. Consequently

    Res12_top = 1152^4*dtop^8*(Ktop*Ltop)^16,

which is a nonzero polynomial form of degree

    8*46+16*(44+11)=1248.

The nonzero leading forms of Nk,Nt add 7+2, proving exact total degree
1257 for P12. Removing the single gate i=Hj from the former primary
circuit gives precisely 139 operations: 93 multiplications and 46
additions/subtractions. The system omits its four-gate product wrapper,
giving 135 operations.

The independently authored checker verifies 100 modular assignments
against a separate quotient-algebra norm, two finite-field degree
diagnostics, all gate/port liveness, 21 synthetic radical-kernel witnesses,
and the hashes of all four actual compact Wang943 coefficient files.
The rational saturation lemma additionally has 49,000 supplementary
finite checks. None of these tests asserts a full accepting K215 run or
replaces the inherited compiler/calibration theorems.
