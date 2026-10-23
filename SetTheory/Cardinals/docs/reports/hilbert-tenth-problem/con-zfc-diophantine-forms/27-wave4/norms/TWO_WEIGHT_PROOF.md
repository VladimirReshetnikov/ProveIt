> Release binding: all new generated artifacts in this directory use the complete mixed-radix Wang943 tuple, B=2^(5^9), selected by COEFFICIENT_BINDING.json. Historical source tuples mentioned below document predecessors or valid alternatives, not the selected numerical instance. The sibling coefficients/COEFFICIENT_PROOF.md proves the full adapter and simultaneous canonical restrictions.

# A two-weight norm in twelve positive integers

## Result, fixed instance, and provenance

The supplied unknowns are exactly

    J,F,alpha,z,h,i,T,s,w,eta,zeta,r > 0.

All other symbols below are polynomial abbreviations, not quantified
variables. The product is an integer polynomial of exact total degree
1081, with a 120-operation division-free arithmetic circuit. A three-equation
system has maximum residual degree 1072 and 115 operations; its final
comparison is free, as in packages 22 and 23. Explicitly computing its
third zero residual costs 116 operations. The sum of squares has degree
2144 and 123 operations. Every binary +,-,* counts, including multiplication
by a numeral. No claim of optimality or a new kernel-checked proof is made.

This combines the normalized root/Pell saturation of packages 20 and 21
with the cheaper quadratic-norm evaluator of package 21. The new step is
to give the first square root a separate, lower-degree weight. Package 22's
monic method was inspected but is not needed for this smaller positive-domain
formula. This is a new algebraic reduction of the inherited compiler interface,
not a new proof of its machine-calibration endpoint.

Sources were inspected at ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`, under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`:

* `20-root12/amalgamation/ROOT12_PROOF.md`, including its weak outer
  bootstrap, rational Pell saturation, and authentic compiler binding.
* `21-norm12/proofs/NORM12_PROOF.md`, sections 3--8, including the coherent
  norm factorization and signed normalized compiler interface.
* `21-norm12/proofs/NORM12_LOWER_DEGREE.md`, which first divides the
  auxiliary conjugate bound by the main radical.
* `21-norm12/arithmetic/build_norm12.py`, adapted with attribution for the
  exact division-free pair-ring evaluator and independent conjugate check.
* `22-monic12/proofs/merger_proof.md`, inspected for the monic alternative
  and its explicit warning that elimination alone does not ensure integrality.

The default whole coefficient tuple is package 20's
`T4-4094-binary-copy-zero-padding-5pow11`, tuple hash
`726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
Its ports are beta=B-1, K0=K, MC, and MF=MF_source (the shifted high mask).
The builder supports replacing this one complete binding by a sibling
`COEFFICIENT_BINDING.json`, after an independent whole-tuple transfer proof.
Individual ports must not be mixed between compilers. All degree statements
hold uniformly for every authentic fixed slice beta>0.

## 1. Common expressions

    q=beta J+1, Cw=q-F-alpha,
    X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)Cw+q-F-z(q-1).

For the normalized strong and auxiliary roots put

    I=ic^2, D=1+Delta I^2,
    Q=(Delta I)^2, d=Q-1,
    v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb.

The new two weights and carrier are

    W=2I(T+Raic), L=1+HW, M=2W,
    S=X+ac+Hr.

For formal indeterminates u,tau,f define

    F(u,tau,f)=d(S-Lu-HM tau)^2-H^2 e+H^2 Baux f.

Let N be the product of these eight factors over all signs of
u=sqrt(G), tau=sqrt(A), and f=sqrt(D). Each sign is an algebraic formal
choice, not a supplied variable. Sign invariance makes the product a
polynomial in the twelve coordinates with integer coefficients.

The requested presentations are

    Nk=1, Nt=1, N=0;
    P=Nk Nt(1+N)-1=0;
    P_sos=(Nk-1)^2+(Nt-1)^2+N^2=0.

The product's semantics, including possible negative unit signs, are proved
below. No congruence or integrality condition is silently discarded.

## 2. Explicit norm evaluator

The following scalar circuit is an alternative complete formula for N:

    a0=H^2 M^2 A, V0=S^2+L^2G, V1=2SL,
    C0=d(V0+a0)-H^2e, C1=dV1,
    Kf=4d^2a0, K0pair=Kf V0, K1pair=Kf V1,
    Z=4H^4(QDv^2)(Qb^2),
    Csq0=C0^2+G C1^2, Csq1=2C0 C1,
    U0=Csq0-K0pair-Z, U1=Csq1-K1pair,
    N0=U0^2+G U1^2-4Z K0pair,
    N1=2U0 U1-4Z K1pair,
    N=N0^2-G N1^2.

To verify, in the quadratic algebra u^2=G put x=S+Lu, V=x^2,
C=d(V+a0)-H^2e, K=4d^2a0 V. Elimination of tau and f gives

    (C^2+K-Z)^2-4C^2K
      =(C^2-K-Z)^2-4KZ.

The displayed pair expressions are the real and u coefficients of this
element; the final norm eliminates u. The + sign in S+Lu is immaterial
because the final product uses both signs of u. The cheap circuit evaluates
HM as 2(HW), using the already computed HW, and uses its square for a0.
The system compares N0^2=G N1^2 rather than computing their difference.

## 3. The product guard and weak outer bootstrap

V1 is even, C1 is even, Csq1 is divisible by 4, and K1pair is divisible
by 8. Hence U1 is divisible by 4, N1 is divisible by 8, and

    N = N0^2 (mod 64).

Consequently N cannot be -2 modulo 4. If P=0, the three integer factors
Nk,Nt,1+N are units. The last cannot be -1, so

    N=0, Nk=Nt=epsilon, epsilon in {1,-1}.

For the system, epsilon=1 from the outset. The inherited authentic-mask
transport bootstrap, valid at both unit signs, gives

    Cw>=0, q>=16, 3q<R<q^4-2, E>=q^4>R+2,
    X>=16, Y>=4096, k=R+epsilon+hE>E and k>R.

In particular c>R, a>=64, Y>=64, Q>=3, and all of
c,I,D,v,b,W,L,M,H are positive. The exceptional boundary Cw=0 is not
discarded. These estimates do not assume any eliminated root is integral
or any root equation holds.

## 4. Coherent roots and the improved separation bounds

If N=0, one factor in its defining product vanishes. Choose the coherent
triple u,tau,f of that factor and define

    y=(S-Lu-HM tau)/H.

Then

    u^2=G, tau^2=A, f^2=D,
    d y^2=e-Baux f=Q(vf-b)^2-1,
    S=Lu+HM tau+Hy.                                      (1)

Consider a finite normal splitting field containing these numbers. Each
conjugate f' is one of the real numbers +/-sqrt(D); each y' satisfies the
corresponding equation in (1). Even if y' is imaginary, its magnitude obeys

    |y'| < sqrt(Q/(Q-1)) (v sqrt(D)+b)
          < (4/3)(v sqrt(D)+b),                          (2)

because Q>=3. For clarity, if Q(vf'-b)^2-1 is negative, its absolute value
is at most 1; otherwise it is at most Q(v sqrt(D)+b)^2-1. The latter bound
exceeds 1 here, so the same estimate covers both cases. No total-reality
assumption is used.

We have sqrt(D)<(a+2)I and sqrt(G)>ac. Divide (2) by sqrt(G). Since R<c,

    |y'|/sqrt(G)
      < (4/3)[ TI(1+2/a) + 1/a + R/(ac)
                    + Ra i^2 c^3(1+4/a+3/a^2) ].       (3)

As a>=64, the coefficient of TI is at most 11/8, the two constant terms
after multiplication by 4/3 sum to less than 1/24, and the coefficient of
Ra i^2 c^3 is at most 4355/3072<3/2. Since TI>=1,
11/8+1/24=17/12<3/2. Thus

    |y'| < (3/2) I(T+Raic) sqrt(G)
          = (3/4) W sqrt(G).                            (4)

The first radical needs only a very modest relative bound. Because c>1,
sqrt(G)<(a+2)c, whereas sqrt(A)>ell=EkY. Also c<k(Y+1), E=XY,
X>=16, and Y>=64. Therefore

    sqrt(G)/sqrt(A)
      < [1+(Y+2)/E](1+1/Y)
      <= (1+66/1024)(65/64)
      = 70850/65536 < 9/8.                              (5)

Set B=HW. Here B>36. Equations (4)--(5), M=2W, and L=1+B give

    HM sqrt(A) > (16/9) B sqrt(G)
      > (7B/4+1) sqrt(G)
      > L sqrt(G)+H |y'|.                              (6)

The middle inequality is exactly B/36>1. The other needed separation is

    L sqrt(G)>H |y'|,                                  (7)

immediate from (4). These two strict bounds hold uniformly for all complex
conjugates. They replace the higher-degree choice M=L in package 21.

## 5. Rationality, integrality, and congruence recovery

If tau were irrational, some automorphism of the splitting field would
send tau to -tau. Subtract its image of (1) from (1). The changed tau term
has magnitude 2HM sqrt(A). The changed u term has magnitude at most
2L sqrt(G), and the two y terms together have magnitude less than
(3/2)HW sqrt(G). Inequality (6), applied with the uniform bound (4), makes
this impossible. Hence tau is rational; tau^2=A makes it an integer.

If u were irrational, an automorphism would send u to -u while fixing
the now rational tau. Subtracting (1) would contradict (7), using the same
uniform conjugate bound. Hence u is rational, and u^2=G makes it an integer.

Now (1) makes y rational. Since Baux=2Qvb>0,

    f=(e-dy^2)/Baux

is rational, and f^2=D makes f a nonzero integer. None of these steps divides
by y or tau, so zero or negative branches have not been lost. Since Q=m^2
with m=Delta I>=2, and V=vf-b is an integer, the last unresolved equation is

    m^2 V^2-(m^2-1)y^2=1.                               (8)

The rational Pell saturation lemma below makes y integral. Reducing (1)
modulo H and using L=1+HW now gives

    u = S = X+ac (mod H),
    gamma=(u-X-ac)/H in Z.

Thus the original main Pell equation and congruence have genuinely been
restored. A bare norm/resultant assertion would not have proved this.

## 6. Rational Pell saturation lemma

If m>=2 and V are integers and rational y satisfies (8), then y is integer.
Write y=p/q in lowest terms, q>0. Then q^2 divides m^2-1. Put
D0=(m^2-1)/q^2, a positive nonsquare integer. Taking absolute values gives
two positive integral Pell solutions

    m^2-D0 q^2=1,
    (m|V|)^2-D0 |p|^2=1.

Neither ordinate vanishes. Let epsilon=x1+y1 sqrt(D0) be the least integral
Pell unit greater than 1. Elementary Pell classification gives m=x_j,
q=y_j, m|V|=x_l, |p|=y_l for positive j,l, where
epsilon^n=x_n+y_n sqrt(D0).

The standard elementary divisibility fact x_j|x_l forces l to be an odd
multiple of j: modulo x_j, epsilon^(2j)=-1, so shifting by 2j negates x_n;
reflection n -> 2j-n also negates it. Reduce l modulo 2j and reflect to
0<=n<=j. If n<j then 0<x_n<x_j, so divisibility is impossible. Hence
l=(2h+1)j. Pell multiplication gives y_j|y_l. Thus q|p, forcing q=1.
This argument uses integral Pell coordinates, not an unjustified assumption
that the quadratic integer ring has no half-integral elements.

## 7. Exact existential equivalence

The recovered integers satisfy the first norm, main norm, normalized strong
norm and auxiliary norm of the inherited compiler:

    tau^2-ell(ell+k)=1,
    (X+ac+H gamma)^2-Delta c^2=1,
    f^2-Delta i^2 c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1,
    Nk=Nt=epsilon.

The identity vf-b=c(Tf-1)-Rf^2 uses f^2=D. Take absolute values of tau,y.
If f<0, change signs of both f and T, preserving Tf. gamma may provisionally
be signed. The inherited signed normalized blank-interface theorem, cited
in package 21 sections 5--8 and package 20's dependencies, is precisely
applicable to these signs and weak outer bounds. It forces epsilon=1 and
recovers an accepting blank K215 tableau. Equivalently one may pass to its
ordinary version by i_ordinary=Delta i, since (i_ordinary c^2)^2=Q.
This use of the signed interface is explicit; positivity of a reconstructed
gamma or quotient is not silently assumed.

Conversely, start with a canonical positive normalized compiler solution,
with main root u=X+ac+H gamma and positive first and auxiliary roots tau,y.
Choose

    r=gamma+W u+M tau+y.

It is a positive integer and yields S=Lu+HM tau+Hy exactly. Hence a coherent
factor of N vanishes, while Nk=Nt=1. This proves completeness for all three
presentations. In particular, the new completeness formula uses M tau,
not the old L tau.

The inherited K215 calibration now gives, formalizably in ZFC,

    no positive solution of P=0  iff  Con(ZFC).

The same holds for the system and sum of squares. This is an equivalence,
not a proof that ZFC is consistent or inconsistent.

## 8. Uniform exact-degree certificate

Give each supplied unknown degree 1 and each fixed port degree 0. The base
degrees are c=5,a=H=6,Delta=12,R=4,ell=11,A=G=22,I=11,D=34,Q=d=46,
v=6,b=38,e=122. The new weights satisfy W=M=27,L=33,S=11.

Unlike package 21's original proof, several top-degree terms now tie. The
following calculation accounts for their cancellations exactly. Write a
subscript * for the highest homogeneous form, and put

    q0=beta J, k0=eta+zeta,
    a*=w s q0^4, c*=k0 s q0^3,
    R*=q0^3(q0-F),
    A*=G*=a*^2 c*^2,
    D*=a*^2 i^2 c*^4, d*=a*^4 i^2 c*^4,
    Z*=d* H*^2 R*^2 D*^2.

Here deg(Z*)=134 and H*=4a*. W*=2R*a*i^2 c*^3. Therefore

    (d V0)*=4Z*, (d a0)*=16Z*, (H^2e)*=Z*,
    C0*=19Z*, K0pair*=256Z*^2.

Z from the evaluator has degree 238, strictly less than 268. Moreover
deg(C1)=90, so G C1^2 has degree 202<268. It follows that

    U0*=(19^2-256)Z*^2=105Z*^2,
    N0*=105^2 Z*^4,
    N*=105^4 Z*^8.

The other branch has deg(U1)<=224, deg(N1)<=492, hence
deg(G N1^2)<=1006<1072. These identities prove, uniformly for beta>0,

    N* = 2^32 105^4 i^48 k0^96 w^80 s^176
                           q0^656(q0-F)^16,
    deg(N)=1072.

This is nonzero in the polynomial ring over every authentic fixed coefficient
slice. Multiplying by

    Nk*=-h w s q0^4,
    Nt*=w(q0-F-alpha)-zq0

gives a nonzero product leading form of degree 1081. Its coefficient at

    J^677 h z i^48 eta^96 w^81 s^177

is +2^32 105^4 beta^677, explicitly nonzero. The sum of squares has unique
highest summand N^2 and exact degree 2144. Finite-field checks supplement
this uniform proof, rather than substituting for it.

## 9. Reproduction and limits

Run `python build_two_weight_norm12.py` with Python 3, without optimization.
The builder emits all three complete circuits, checks all gates and ports
are live, counts operations, checks degree upper bounds, compares 24 signed
exact assignments with independent multiplication of all eight conjugates,
checks the modular guard, and checks top forms in two finite-field slices.
`TWO_WEIGHT_CHECKS.json` records the receipt. The code is self-contained
and uses only Python's standard library.

These are finite algebra and implementation checks. They do not search for
an accepting K215 computation, expand huge fixed coefficients, or rerun the
inherited formal machine endpoint. The unbounded semantic argument is the
mathematical proof above together with the explicitly named compiler and
calibration dependencies. No 11-variable construction has been established
by this work.
