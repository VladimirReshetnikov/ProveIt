# A fixed-input specialization: 16 positive unknowns, 73 arithmetic gates

## Scope and exact imported theorem

This note gives an ordinary polynomial and a seven-equation alternative.
The construction specializes the **admissible fixed-program compiler** of
`Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`
at repository snapshot `cdd582bec13f908df3711fa9e05d1ddac368a5db`.
That theorem is a mathematical proof with source/identity reviews, not a
Lean or Rocq formalization. Its full helical compiler and mask hypotheses
are retained. Arbitrary positive values of the coefficient ports are not
valid program instances. The K215-to-program bridge and actual coefficient
recipes are separate deliverables.

The ordinary arithmetic input is fixed to x=1. Its decoded End position
is cell2x, so the normalized machine is run at **raw input2**, not raw
input1. Equivalently define S={x>0: the normalized machine accepts2x}.
The normalized K215 program ignores its input, so this convention does not
change its halting predicate. Let d,b,B=2^d, DC,DR,MC,MF_native be the
compiler constants, with d>=4 and b positive odd. The five numeral ports are

    Bm1 = B-1,
    K = DC+B*DR,
    MC = MC,
    MF = MF_native+B-1,
    W0 = 2^(2*d+b).

In particular MF is the shifted port: do not substitute MF_native directly.
W0 is a fixed integer coefficient. Its exponent contains no unknown.

The resulting polynomial has a positive integer zero exactly when the fixed
compiled program accepts raw input2. For a program accepting raw input2 exactly
when K215 halts, this gives the requested inconsistency predicate, subject
to the repository's K215 consistency bridge.

## 1. Complete compact polynomial specification

All sixteen unknowns are strictly positive integers:

    J,F,alpha,t,f,h,i,T,s,w,tau,eta,zeta,y,Z,gamma.

Define the following polynomial abbreviations (none is an additional
existential variable):

    q=(B-1)J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    C=Z+W0,
    G=q^2-qF-Z,
    R=G(q^2-1)+(MC+q*MF)J,
    V=c(Tf-1)-Rf^2,
    L=E(kY),
    Kaux=(i*Delta*c^2)^2.

The seven factors are

    N0=tau^2-L(L+k),
    N1=D^2-Delta*c^2,
    Na=Kaux*(V^2-y^2)+y^2,
    Nk=k-hE-R,
    Nt=(K+w)C+(q-F)-t(q-1),
    Ns=Delta*f^2-Kaux,
    M=1+(q-F-Z-alpha-C)^2.

The claimed ordinary polynomial is

    P = N0*N1*Na*Nk*Nt*Ns*M-Delta.                 (P)

There are no variable exponents, floor functions, digit predicates,
divisibility predicates, implicit bounded universal quantifiers, or
unbounded lists in this definition. The straight-line expansion is the
literal74-parent-derived,73-row array in `fixed_input73.json`.

A simpler system for hand checking is

    N0=N1=Na=Nk=Nt=1,
    Ns=Delta,
    q-F-Z-alpha=C.                                (S)

The64-parent-derived,63-row array in `fixed_input63_system.json` computes
every comparison operand. The comparison count is seven.

## 2. Cancelling the discriminant and recovering unit equations

Delta=(a+1)(a+3)>0 on the entire positive witness domain. Write

    Ns0=f^2-Delta*i^2*c^4,

so that Ns=Delta*Ns0 identically. A zero of (P) therefore gives

    N0*N1*Na*Nk*Nt*Ns0*M=1.                        (1)

Each factor is an integer unit. Since M is a positive integer, M=1. Thus

    q=F+2Z+alpha+W0,
    C=Z+W0,
    0<C<q,
    F+Z<q,
    W0<q.                                         (2)

N1 and Ns0 cannot be-1 modulo4: Delta=(a+2)^2-1 is0 or3 modulo4, and
a square minus Delta times a square is never3 modulo4. Since Kaux is an
integer square, Na modulo4 is either y^2 or V^2 and likewise cannot be-1.

For N0 put V0=XY^2>1. Then L=V0*k, so

    N0=tau^2-V0(V0+1)k^2.

The negative Pell equation for V0(V0+1) has no integer solutions when
V0>1. The descent in `complete75_coupled_index_linear88.md`, section2,
applies directly: from x^2-V0(V0+1)z^2=-1, with positive minimal z,
the inverse fundamental unit gives a smaller positive
z'=(2V0+1)z-2x. Hence N0=1.

Consequently N0=N1=Na=Ns0=1, while Nk=epsilon and Nt=nu with
epsilon,nu in{-1,1} and epsilon*nu=1. Recovering the index sign is a
real proof obligation; it is not a consequence of taking a product.

## 3. Positive auxiliary reconstruction and exact main index

This section uses precisely the input-independent norm/rank argument in
`complete85_auxiliary_bezout_projection.md`, sections3-4. Its input norm
is absent here; none of those local bounds uses that norm. The positive
gamma coordinate replaces rho+sigma.

The admissible masks and (2), with q>=B>=16, give

    (2q-1)(q^2-1)<R<q^4-q^3,
    E=wsq^4>=q^4>R+2,
    a=E+Y>R+2.                                    (3)

These are pretyping inequalities. No dyadic or accepting-history
conclusion has yet been assumed.

Ns0=1 gives f^2=1+Delta*i^2*c^4. In particular f>c^2>2c, c>2, and

    Kaux-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.           (4)

The auxiliary equation can be written

    Kaux*V^2-(Kaux-1)y^2=1.

If v=|V|>1, then
v^2-1=(Kaux-1)(y^2-v^2)>0, so y>=v+1 and v>=2Kaux-1.
But T>0 implies V>-Rf^2-c, and (4) excludes all negative V with
|V|>1. The cases V=0 or V=+-1 are impossible: V is congruent to -c
modulo f, while 2<c<f/2. Hence V>0.

Define integers

    o=cT-Rf,
    j=Tf-R*Delta*i^2*c^3-1.

The identities

    of-c=V,
    jc=V+R

hold at Ns0=1. Thus o and j are strictly positive, and V=of-c=jc-R.

Let A=a+2 and P0=2XY^2+1. The first Pell norm gives

    tau=chi_P0(n), k=2psi_P0(n), n>=1.

Since P0=1 modulo E and k=R+epsilon+hE,

    2n=R+epsilon modulo E,
    n>=(R-1)/2>=24.

The main norm gives D=chi_A(p), c=psi_A(p). Since P0>A and c>k,
p>n. The elementary Pell growth bounds give c>A*Delta^2, c>2p,
and c>2R. The full strong-square rank lemma applies with i_old=Delta*i:

    (i_old*c^2)^2=Delta*(f^2-1),
    f=chi_A(m), c divides m, m>=c>2p.

The signed auxiliary step-down lemma, using V=of-c=jc-R and the strict
bounds0<R<c/2 and0<p<c/2, gives p=R. These are the hypotheses and
conclusion of the independently reviewed generic-rank and step-down
lemmas used by the F85 source, not an invocation of its whole compiler
theorem with missing premises.

Writing2n=R+epsilon+vE, with v>=0, (3) and n<p=R exclude v>=1:
otherwise2n>=R-1+E>2R+1>2p. Only E>R+2 is used; the stronger
symmetric-scale estimate E>2(R+2) is neither assumed nor needed.
Thus2n=R+epsilon. If epsilon=-1 then p=2n+1. Pell duplication and
monotonicity imply

    psi_A(2n)>=A*k,
    c=psi_A(2n+1)>A*k>k(Y+1),

contrary to kY<c<k(Y+1), which follows from eta,zeta>0. Therefore
epsilon=1 and nu=1. All six unscaled factors equal1, proving that (P)
implies (S). The converse follows immediately by multiplication.

## 4. Dyadic recovery and restoring the omitted input bridge

The input-independent asymmetric-scale lemma gives X=2^R. Its use here
can be made explicit. Write R=2r+1, k=2psi_P0(r+1). The retained lower
Pell ratio implies

    Y>((X+1)^(2r)/X^r)/2-1>X^r/3,
    a>X^(r+1)/3>2^R.

The projected Pell sequence E_A(j)=chi_A(j)-a*psi_A(j) starts at1,2,
and satisfies E_A(j)=2^j modulo H. The main-root equation gives
E_A(R)=X+gamma*H. Both X and2^R lie strictly between0 and a, so their
congruence modulo H=4a+3 forces equality. This is section3 of
`complete75_asymmetric_scale_tradeoffs.md`, with gamma replacing
rho+sigma; the input norm is unused.

Since X=wq, q is a power of two, say q=2^ell. The lower bound for R
in (3) gives R>3q>3ell, so q^3 divides X. Set w_old=X/q^3>0.
The repunit equation B-1 divides q-1 also yields q=B^N, although
restoring the input bridge needs only the dyadic conclusion.

Put u=2d+b, so W0=2^u. By (2),2^u<2^ell and hence u<ell<R.
Both u and R are odd, so R>=u+2.

The omission of the old subtraction2d from the raw-bound slack needs
its own proof. Since q and W0 are powers of two and W0<q, q>=2W0.
Using (2),

    q-C=(q-W0+F+alpha)/2>W0/2
        =2^(2d+b-1)>=2d.

Thus **alpha_raw=q-C-2d is a strictly positive integer**. This restores
the raw75 bound C+alpha_raw+2d=q. No unjustified positive restoration
alpha_old=alpha-2d is used; that expression need not be positive.

For the omitted input coordinates set

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta,
    phi=c-kappa,
    rho=(E_A(u)-W0)/H.

All are positive integers. For odd u, psi_A(u)=u modulo Delta; u>=3
gives psi_A(u)>u. The inequality u<R gives phi>0. The recurrence
E_A(u)=2^u modulo H proves rho integral. More explicitly,
E_A(u)=2psi_A(u)-psi_A(u-1)>psi_A(u)>=(2A-1)^(u-1)>2^u
because A>=3 and u>=3, hence rho>0. They satisfy exactly

    kappa=u+delta*Delta, c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W0+a*kappa+rho*H.

If one also wants the historical projected coordinate sigma, it is
gamma-rho>0. Indeed E_A(R)-E_A(u)>A>X for R>=u+2, and

    H*(gamma-rho)=E_A(R)-E_A(u)-X+W0>0.

The raw source does not need sigma.

Finally the transport equation Nt=1 gives the original raw transport
quotient

    z_raw=t-1+wC>0,

because X=wq and
(K+X)C-F=(t-1+wC)(q-1). Restore i_raw=Delta*i, o,j as in section3,
tau unchanged, h0=h, W=W0, all positive. Together with w_old,
alpha_raw, and the input coordinates above, these satisfy all nineteen
equations of the original raw75 source at x=1. Its theorem therefore
proves acceptance of the compiled program at raw input2. This is a concrete
restoration of every missing premise, not a claim of an identical
positive-zero set to F84.

## 5. Completeness

If the compiled program accepts raw input2, the reviewed F84 universal theorem supplies
eighteen positive coordinates. Its input bridge gives W=W0 and every
unscaled factor equals1. Discard delta,rho,sigma, put

    gamma=rho+sigma,
    alpha_new=alpha_F84+2d,

and keep the other coordinates. The equality
C=q-F-Z-alpha_F84-2d=Z+W0 becomes exactly the new budget equation.
Every remaining factor is unchanged, so the new tuple satisfies (S)
and (P). Therefore both directions of the fixed-input theorem hold.

## 6. Exact size and degree

The complete polynomial has41 multiplications and32 additions or
subtractions:73 paid binary gates. A square costs one multiplication;
every use of a nontrivial numeral in an arithmetic gate is charged.
The seven-equation schedule has34 multiplications and29 additions or
subtractions:63 arithmetic gates plus seven comparisons. All supplied
ports and all gates are live. The number16 counts actual existential
coordinates; the polynomial abbreviations do not add unknowns.

For the degree calculation put

    Q=(B-1)J, k0=eta+zeta,
    T2=wZ-tQ, W1=Q-F-2Z-alpha.

The factor degrees in the order N0,N1,Na,Nk,Nt,Ns,M are

    22,18,60,7,2,46,2.

Their leading forms multiply to

    -8 Q^91 h gamma i^4 k0^13 w^13 s^26 T^2 f^2 T2 W1^2.     (3)

One explicit monomial in (3) is

    J^94 h gamma i^4 eta^13 w^13 s^26 t T^2 f^2,

with coefficient8(B-1)^94, nonzero for every valid B>1. Thus the total
degree is exactly157 uniformly over all admissible fixed program
instances. Subtracting the degree12 discriminant cannot affect it.
The system's largest equation degree is60; its sum-of-squared-residuals
polynomial has exact degree120 (the auxiliary residual is the unique
degree60 residual). This gives a lower-degree alternative at a larger
arithmetic cost.

The checker executes all73 rows over exact integer univariate coefficient
lists with every witness replaced by t. At the diagnostic coefficient
tuple Bm1=15,K=11,MC=2,MF=19,W0=8192, it attains degree157 with the
predicted leading coefficient. These diagnostic numerals are explicitly
not claimed to compile K215 or any valid universal program.

## 7. Evidence and limitations

`verify_fixed_input.py` uses Python's standard library. It verifies the
73/63-row closure and liveness, the16-coordinate interface, operation
ledgers,64 signed all-value cross-product identities against the pinned
full F84 source, exact factor degrees, and an exact degree157 polynomial
specialization. Assertions are not used for validation, so Python-O does
not erase the checks.

These checks validate arithmetic source transformations. They do not
prove the imported Pell lemmas, compile a valid machine by themselves,
materialize an astronomical accepting witness, or establish ZFC
consistency. The semantic theorem is the proof in sections2-5 plus the
explicitly stated repository dependencies.

No global optimality claim is made. The construction improves the
existing ordinary-input universal84-gate18-witness expression by fixing
the input and precomputing its endpoint marker as a numeral. A
universal ordinary-input circuit still has to pay for that marker's
variable-input representation.

