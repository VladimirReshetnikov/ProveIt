# Twelve positive unknowns: degree 1081 in 116 binary operations

## Result and scope

This note gives a new ratio separation of the root merger in package 20,
using the economical norm evaluation of package 21. At the inspected
ProveIt snapshot `a477d0fc8b6feda53796835564a988015e744d4d`, the best stated
twelve-positive-variable degree was 1145 (123 operations, package 20),
and the fewest single-equation operations were 116 (degree 1353, package
21). The present product has exact degree **1081**, also **116 operations**.
The three-equation presentation has maximum degree **1072** in **111
operations**, or **110 operations** after the inherited positive transport
shift, versus the previous 112-operation systems. Comparisons are
free in the inherited metric; every binary +, -, * is charged, including
multiplication by fixed numerals. Twelve means supplied positive unknowns,
not polynomial abbreviations or fixed coefficient ports.

The proof uses the same whole, authenticated native-compiler coefficient
tuple and inherited K215 logical endpoint as those packages. It is an
ordinary mathematical reduction formalizable in ZFC, not a new Lean or
Rocq certificate. Do not reuse its ratio bound over signed s.

## 1. The polynomial definitions

The twelve positive unknowns are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,r.

Use one whole native tuple `(beta,K0,MC,MF)`, with beta=B-1 and **shifted**
MF. Define

    q=beta J+1, Cw=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H=(a+2)^2-1,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nk=k-hE-R,
    Nt=(K0+w)Cw+(q-F)-z(q-1),
    ell=EkY, A=1+ell(ell+k), G=1+Delta c^2,
    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2,
    d=Q-1, v=cT, b=c+RD,
    P=QDv^2, U=Qb^2, e=P+U-1, Baux=2Qvb.

The changed weights are

    M=kI^2+T^2, L=1+2HM, W=X+ac+Hr.

For temporary formal roots u^2=G, t^2=A, f^2=D, set

    N= product_(u=+-sqrt(G),t=+-sqrt(A),f=+-sqrt(D))
         [d(W-Lu-HMt)^2-H^2 e+H^2 Baux f].

This conjugate product is an integer polynomial in the original twelve
unknowns. The root symbols are not quantified unknowns. Each emitted packet
binds its fixed ports through `../coefficients/COEFFICIENT_BINDING.json`.
A fully explicit
division-free binary circuit is emitted by `build_ratio12.py`. The single
equation is

    Nk Nt (1+N)-1=0.                              (P)

The system is Nk=1, Nt=1, N=0. To save one arithmetic gate the JSON system
compares the two terms of the final norm directly, instead of subtracting
them and comparing their difference to zero.

## 2. The explicit norm evaluator

All quantities here are polynomial abbreviations. Put

    Z0=W^2+L^2G, Z1=2WL,
    n=(HM)^2 A,
    C0=d(Z0+n)-H^2e, C1=dZ1,
    Kf=4d^2 n, K0p=Kf Z0, K1p=Kf Z1,
    j=4H^4 PU=H^4 D Baux^2,
    Csq0=C0^2+GC1^2, Csq1=2C0C1,
    V0=Csq0-K0p-j, V1=Csq1-K1p,
    N0=V0^2+GV1^2-4jK0p,
    N1=2V0V1-4jK1p,
    N=N0^2-GN1^2.

The identity behind the evaluator is

    (C^2+j-K)^2-4jC^2 = (C^2-K-j)^2-4jK,

in the quadratic ring with u^2=G. This is exactly the same norm as the
displayed eight-factor product. For the system the last comparison is
`N0^2=G N1^2`. Fixed `K0` and temporary `K0p` are distinct names.

## 3. Unit extraction and the inherited weak bootstrap

For integral supplied variables, N1 is divisible by 8. Indeed Z1 is even,
C1 is even, Csq1 is divisible by 4, K1p is divisible by 8, V1 is divisible
by 4, and N1=2V0V1-4jK1p is divisible by 8. Consequently N is a square
modulo 64, in particular 1+N cannot be -1 modulo 4.

At a positive solution of (P), its three integer factors are units.
Therefore N=0 and Nk=Nt=epsilon with epsilon in {1,-1}. For the system
epsilon=1 immediately. The package-20 weak transport bootstrap, unchanged
because none of Nk,Nt,R,X,Y,k,c was altered, gives

    q>=16, X>=16, Y>=4096, Cw>=0,
    0<R<q^4-2, R>3q>=48,
    E>=q^4>R+2, k=R+epsilon+hE>E, R<k,
    kY<c<k(Y+1)<2kY.

No root square, gamma sign, or positivity of an omitted coordinate is
assumed here. In particular all of D,Q,d,v,b,P,U,M,H,L are positive.

## 4. A stronger low-degree inner weight

Write a0=a+2 (only in this section). The weak bounds give a0<2E,
ell=kEY>a0 c/4, and ell>E^2Y>8a0^2. Hence

    A>a0^2 c^2/16,       A>64a0^4.

Also D<a0^2I^2. Since c<I^2 and R<k, we have

    b=c+RD<2k a0^2 I^2.

For M=kI^2+T^2, the elementary square inequality gives
M^2>=4kI^2T^2. Therefore

    A M^2 > (k/4) D v^2 > 8 D v^2,
    A M^2 >= A k^2 I^4 > 16 b^2 > 8 b^2.

Averaging these strict bounds gives A M^2>4(Dv^2+b^2). As d=Q-1>=Q/2,

    d A M^2 > 2 Q(Dv^2+b^2)=2(e+1).             (1)

This strengthens package 20's constants sufficiently to omit its factor
2 in M. The large q,Y bounds are inherited from the exact compiler; the
argument is not a claim about arbitrary small parameter values.

If f'=+-sqrt(D) and y' is any complex number satisfying

    d (y')^2=e-Baux f',

then

    d|y'|^2 <= e+Baux sqrt(D)
               < Q(v sqrt(D)+b)^2
               <=2Q(Dv^2+b^2) < dAM^2.

Thus every such conjugate satisfies

    |y'|<M sqrt(A).                              (2)

## 5. Ratio separation: the improvement

The useful comparison is between the first and main radicands, rather
than an absolute bound for the first root. Since c>kY and Delta>(E+Y)^2,

    G-A > k^2[(E+Y)^2Y^2-EY(EY+1)]
          =k^2[EY(2Y^2-1)+Y^4] >0.              (3)

Thus sqrt(A)<sqrt(G), uniformly for the positive supplied domain.

Let F(x) be the inner product over the four choices t=+-sqrt(A),
f=+-sqrt(D) of d(x-Mt)^2-e+Baux f. Every complex root of F has the form
x=Mt+y' and therefore, by (2),

    |x|<2M sqrt(A)<2M sqrt(G).                   (4)

At N=0, some u=+-sqrt(G) gives x=(W-Lu)/H with F(x)=0. If G were not an
integer square, quadratic conjugation would show that
x'=(W+Lu)/H is also a root. Their distance is

    |x'-x|=2L sqrt(G)/H >4M sqrt(G),

while (4) makes it less than 4M sqrt(G), a contradiction. Hence G is an
integer square and the selected u is integral. Moreover W>0 and u cannot
be negative, since then

    W=Lu+Hx <=-L sqrt(G)+H|x|
              <-L sqrt(G)+2HM sqrt(G)=-sqrt(G)<0.

Consequently u>0 and x is rational.

This is why L=1+2HM suffices. Package 20 used the much larger
L=1+2HM(ell+k); the extra factor ell+k is unnecessary when one compares
the inner root bound to the separation of the two main-root branches.

## 6. Recovering the inner integer roots

For rational x set

    C=d(x^2+M^2A)-e,
    V=C^2+D Baux^2-4d^2x^2M^2A.

Equation (1) gives C>e+2>0. Also x cannot be zero. Indeed

    F(0)=[(dM^2A-e)^2-D Baux^2]^2>0,

because dM^2A-e>e+2 and sqrt(D)Baux<=e+1 by the elementary arithmetic-
geometric mean inequality. From F(x)=0 we obtain

    f=-V/(2C Baux),
    t=(C+Baux f)/(2dxM),
    y=x-Mt.

These are initially rational, with f^2=D and t^2=A. Thus f and t are
integers. Expanding the defining equations gives

    Q(vf-b)^2-(Q-1)y^2=1.                        (5)

Here Q=(Delta I)^2 and vf-b is integral. The rational auxiliary-Pell
saturation lemma used in packages 20-22 therefore makes y integral.

For clarity, that lemma says: if m>=2, V is an integer, and rational y
satisfies m^2V^2-(m^2-1)y^2=1, then y is an integer. Write y=A0/B0 in
lowest terms. Then B0^2 divides m^2-1. For d0=(m^2-1)/B0^2, the two
integer Pell solutions are (m,B0) and (m|V|,|A0|). If epsilon is the
fundamental positive integer Pell unit, write their abscissas chi_j and
chi_l. The divisibility chi_j|chi_l forces l to be an odd multiple of j:
reduce l modulo 2j using chi_(n+2j)=-chi_n mod chi_j, then reflect into
0<=n<=j, where 0<chi_n<chi_j for n<j. The corresponding ordinate
divisibility gives B0|A0; coprimality forces B0=1. This argument uses the
ordinary integer Pell group, not half-integral units.

## 7. The main congruence, compiler soundness, and completeness

Now x=Mt+y is integral. The equation W=Lu+Hx and L=1+2HM give
u=W=X+ac modulo H. Thus gamma=(u-X-ac)/H is integral and

    (X+ac+Hgamma)^2-Delta c^2=1.

The restored first norm is t^2-ell(ell+k)=1. Already the weak outer
bounds give c>k>E=XY>X. Since u>0 and Delta>(a+1)^2, we have
u>(a+1)c and hence gamma H>c-X>0. So gamma is positive, not merely
provisionally signed. No extra Pell-index classification is needed for
this sign recovery.

The restored strong and auxiliary equations are

    f^2-Delta i^2c^4=1,
    Q[c(Tf-1)-Rf^2]^2-(Q-1)y^2=1.

The identity vf-b=c(Tf-1)-Rf^2 uses f^2=D. Take absolute values of t,y.
If f<0, replace (f,T) by (-f,-T). These are exactly the coordinates and
allowed signed quotient of package 09's normalized signed-quotient
interface, used and reproduced in package 20. Its soundness theorem
forces epsilon=1 and recovers a blank halting run of K215. Combining with
the K215 syntactic-refutation endpoint yields ZFC-inconsistency.

Conversely, take a canonical positive normalized blank-compiler witness.
Let u=X+ac+Hgamma>0, t>0, y>0 be its roots and put

    r=gamma+2Mu+Mt+y.

Then r is positive, and W=b0+Hr=Lu+H(Mt+y). The associated factor of the
eight-factor norm vanishes. Nk=Nt=1, so both the system and (P) hold.
This proves exact existential equivalence; consequently ZFC proves that
unsolvability in positive integers is equivalent to Con(ZFC).

## 8. The shifted 110-operation system

Replace Nt=1 by

    (K0+w)Cw=F+z(q-1).                          (Tshift)

The same twelve supplied names are used, but here z is the old transport
coordinate minus one. All other definitions and the other two equations
are unchanged. Every positive shifted solution gives an unshifted one
by z_old=z+1, so soundness follows from the proof above. Conversely a
positive unshifted solution reconstructs the authentic compiler, hence
Cw>0 and X=wq=2^R with R>3q. Thus w>q>F and

    (K0+w)Cw-F=(z_old-1)(q-1)>0.

Therefore z_old>=2 and z=z_old-1 is positive. This is the same zero-set
coordinate shift proved in `22-monic12/proofs/RETAINED59_PROOF.md` and
requires the compiler theorem only in the completeness direction, after
the main proof is finished; it is not used as a premature weak bound.

The gate `trans1=trans0+(q-F)` is deleted, and
`Nt=trans1-z(q-1)` is replaced by `transport_rhs=F+z(q-1)` with a direct
comparison to trans0. This saves exactly one operation. The shifted
system's ledger is **110 total, 72 multiplications, 38 additions or
subtractions**. Its residual degrees remain 7, 2, and 1072. The product
polynomial retains the unshifted z and its 116-operation count.

## 9. Exact degree, uniformly in every valid coefficient tuple

All supplied unknowns have degree one, fixed coefficient ports degree
zero. The unchanged data have degrees

    c=5, a=H=6, Delta=12, I=11, D=34, Q=d=46,
    ell=11, A=G=22, R=4, b=38, P=92, U=e=122.

The changed data have degrees

    M=23, HM=L=29, W=11, n=80,
    Z0=80, Z1=40, C0=134, C1=86.

In C0 the unique highest part is -H^2e (degree134); d(Z0+n) has degree
at most126. Hence Csq0 and V0 have unique highest part H^4e^2
(degree268). V1 has degree220, j has degree238, K0p degree252, and K1p
degree212. It follows that N0 has unique highest part H^8e^4 (degree536),
whereas N1 has degree at most488. The final subtraction cannot cancel:
N0^2 has degree1072, while GN1^2 has degree at most998. Thus

    deg(N)=1072,       deg(P)=1072+7+2=1081.

For an explicit nonzero leading-form certificate put q0=beta J and
k0=eta+zeta. Then

    N_top=2^32 i^48 k0^96 w^80 s^176 q0^656(q0-F)^16,

and the product leading form is this multiplied by

    (-h w s q0^4) [w(q0-F-alpha)-zq0].

For example, the coefficient of

    J^677 h z i^48 eta^96 w^81 s^177

is +2^32 beta^677, which is nonzero for every valid beta>0. This is a
uniform exact-degree proof, not an inference from generic numerical
specialization.

## 10. Reproduction and limits

Run `python3 build_ratio12.py`. It emits the three JSON arithmetic circuits
and their gate ledgers, rejects dead gates and unused supplied ports, and
checks 40 signed assignments against an independent eight-dimensional
conjugate-product implementation. It also checks the transport shift, two
nonvanishing modular evaluations of the analytic leading forms, and 18
isolated canonical-root/inverse-reconstruction fixtures, including negative
strong roots. All checks raise explicit exceptions and remain active under
`python3 -O`. These finite checks establish only the
reported arithmetic identities on the tested assignments and corroborate
the circuit transcription; the proofs above establish unbounded
equivalence. No giant full K215 witness or expanded coefficient is
evaluated by the diagnostics.

The construction is more efficient within the reviewed twelve-positive-
variable family. It does not beat the existing 67-operation equation in
total operation count, the nine-natural-variable Jones construction in
unknown count, or the low-degree lifted systems in degree. It is not a
global minimality theorem.

## Provenance

All cited source paths are under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`
at commit `a477d0fc8b6feda53796835564a988015e744d4d`:

- `20-root12/amalgamation/ROOT12_PROOF.md`: normalized interface, weak
  bounds, inner root recovery, positive gamma recovery, signed quotient.
- `20-root12/amalgamation/dependencies/09_ROOT_AMALGAMATION_PROOF.md`:
  the inherited package-09 interface used by package20.
- `21-norm12/proofs/NORM12_PROOF.md` and
  `21-norm12/arithmetic/build_norm12.py`: economical norm evaluator and
  parity finalizer.
- `22-monic12/proofs/merger_proof.md`: independent presentation of the
  rational auxiliary-Pell saturation lemma.
- `22-monic12/proofs/RETAINED59_PROOF.md`: positive transport-coordinate
  shift used for the 110-operation system.

The novelty here is the bound A<G and ratio separation with L=1+2HM,
together with the strengthened constants permitting M=kI^2+T^2.

