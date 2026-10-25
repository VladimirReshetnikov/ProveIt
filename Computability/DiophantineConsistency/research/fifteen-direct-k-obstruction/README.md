# Taking k as a free positive input loses the native calibration

This is a CODE-FREE ordinary proof proposed for independent review. It
concerns only the proposed change that replaces the positive input zeta
by a positive input k and deletes k=eta+zeta from the maintained P66
formula. Every other abbreviation, factor, fixed port and positivity
requirement is retained. The changed equation has a symbolic positive
zero on the **actual accepted indexed four ports**, constructed below
without a halting computation. At that zero eta>k, so the missing positive
remainder k-eta cannot be restored.

The maintained fifteen-positive66/157 equation is unchanged. Its old
positive domain requires eta<k. This is an obstruction to the proposed
one-addition deletion, not a counterexample to that equation, its ordinary
calibration, or Con(ZFC). No new circuit, operation/degree endpoint,
numerical tuple, coefficient packet or execution result is emitted. This
note is not accepted until the separately requested ordinary reviews finish.

## 1. The entire proposed polynomial and exact fixed ports

The fifteen proposed positive integer inputs are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,k,y,gamma.

They replace only zeta by k. Define all abbreviations by

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    ell=E*k*Y, c=k*Y+eta, a=E+Y, H=4*a+3,
    Delta=a^2+H=(a+2)^2-1, D=X+a*c+gamma*H,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    S=i*Delta*c^2, V=f^2*(c*T-R)-c,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2, Nk=k-h*E-R,
    Nt=(K+w)*C+(q-F)-z*(q-1), Ns=Delta*f^2-S^2.

The proposed output is exactly

    P_direct=N0*N1*Na*Nk*Nt*Ns-Delta.              (1)

K denotes the maintained port K0. All four ports are the single coherent
directly indexed BFS943 tuple accepted with compact66:

    rho=2^67, L=8807, d=590069, B=rho^L=2^d,
    beta=B-1, K=DC+B*DR, DR=rho^42,
    MF=MF_source=MF_native+beta.

The accepted indexed recipe supplies DC and the two masks. In particular

    0<DC,DR<B, K>0, 0<MC,MF_native<beta,
    MC=2 mod4, MF_native=4 mod8.

Every DC monomial has positive rho exponent, so DC=0 modulo4. MF is
shifted exactly once. The complete compact66 and indexed parent folders,
their binding records and all four existing raw port hashes are pinned.
No original compact44 K, sorted-BFS K, different alphabet, machine or
free-port toy value is substituted.

## 2. Exact source facts used

All paths here are relative to Computability/DiophantineConsistency.
SOURCE_PINS gives exact bytes/hashes and the two whole parent inventories.
These source facts are ordinary accepted mathematical dependencies; their
applications, finite verifiers and proof assistants are not rerun here.

* `candidates/one-page-compact66/PROOF.md`, sections1,2,4, gives the
  complete maintained P66 formula, whole indexed binding, normalized
  strong Pell interface and squared-modulus auxiliary construction.
* `research/indexed-tile-enumeration/PROOF.md`, section2, lines56--108,
  gives this rho,B,DC,DR,mask tuple. Section3, lines119--168, gives the
  exact orders, lifting and unit certificates and the Boolean subset
  argument for the actual rank, with NEW indexed DC. In particular
  this is not a transfer of numerical residues from another K.
* Its `NATIVE_CERTIFICATE.json` records those same finite controller
  premises. Its `coefficients/BINDING.json` and compact66's complete
  coefficient/calibration bindings identify all four whole ports.
* `con-zfc-diophantine-forms/36-small-tuple/coefficients/source_proofs/`
  `BLANK_HELICAL_PROOF.md`, lines92--116, gives the exact coefficient-
  independent change of rank and explains the target R=d*u modulo dN
  for X=2^R, with no factor2 or additive1. No valid tableau hypothesis
  is used in the algebraic difference identity itself.
* In the same source_proofs directory, `ORDINARY_BLANK_PROOF.md`,
  sections4--7, gives the Pell classifications, strict ratio window,
  elementary Pell growth and the population decoder that the old
  remainder interval supports. `INHERITED_P67_PROOF.md` under
  `36-small-tuple/proofs/`, sections4--5, retains that same interval.
* `con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md`, section2,
  is the aggregate complement lemma, used only to identify why the
  deliberately incomplete Start cell below is not a valid native cell.

The current compact66 source and native data are sufficient. The original
machine/refutation interpretation is not invoked to construct this zero.

## 3. Rank tuning without a native high-mask assumption

Put lambda=581197 and kappa=lambda-1=581196. The accepted indexed facts
are: lambda is prime; d=67*8807 is coprime to lambda; the orders of B
modulo67,8807,lambda are66,4403,581196; their relevant orders divide
kappa; and

    B^kappa mod lambda^2=182964883980 !=1.

Thus B^kappa=1 modulo d and v_lambda(B^kappa-1)=1. The indexed unit
table, with Hctrl=1+B*DC+B^2*(DR+1), is

| Prime | B | B^2-1 | Hctrl |
| --- | ---: | ---: | ---: |
| 67 | 46 | 38 | 23 |
| 8807 | 456 | 5374 | 3359 |
| 581197 | 348469 | 573553 | 404489 |

Choose fixed geometric dimensions

    u0=lambda, h0=lambda^3, N=u0*h0=lambda^4,
    T0=N/lambda=lambda^3, q=B^N, J=(q-1)/(B-1),
    M0=N-T0-lambda+3, U=K+B^u0.

Here u0 is a geometric shift, not the polynomial input w; h0 is not
the polynomial input h. Since lambda>1000 and d<1000000, lambda^2>d.
Therefore N>d*lambda^2, h0>lambda, T0>d*lambda, and u0<T0, exactly the
size premises of the accepted subset argument. All these dimensions are
chosen without a computation tableau.

Let the available cell positions be the disjoint set

    Aset={2+kappa*j:0<=j<T0} union{3}.            (2)

Its maximum is M0. Every subset Q of Aset defines integers

    W_Q=sum_(j in Q) B^j,
    C_Q=1+rho^1063*W_Q, F_Q=U*C_Q.              (3)

In native cell notation C_Q has only selector0 at the origin and a
Boolean subset of the ignored low dummy1063 bits elsewhere. It has no
copy or anchor bits. The distinct cell positions in (2) are positive,
so each B-digit of C_Q is either0,1 or rho^1063, all strictly below B.
Consequently C_Q<B^(M0+1). Also K=DC+B*DR<B+B^2<B^3<=B^u0, hence

    U<2B^u0, F_Q<2B^(M0+u0+1).

Because u0<T0 and lambda>=5,

    M0+u0+1<=N-lambda+3<=N-2.

Thus, uniformly for **every** subset Q,

    2C_Q+F_Q<4B^(N-2)<q/3.                     (4)

The last inequality uses B>=16. This direct magnitude proof needs no
valid local tile, native high-mask relation, carry estimate or canonical
tableau assumption. It implies that F_Q,C_Q and alpha_Q=q-F_Q-C_Q are
strictly positive. It also shows that the products are ordinary integers
below q, without modular wrap. Every selected cell and its translates
by1 and u0 are below N, since M0+u0+1<=N-2.

At fixed q,J define the entire actual outer rank, not a surrogate, by

    R(C,F)=[q(q-F)-C]*(q^2-1)+(MC+q*MF)*J.

Let R0=R(1,U). Define

    Gamma=rho^1063*(q^2-1)*(1+q*U).

Equations (3) give the exact identity, for every subset Q,

    R(C_Q,F_Q)=R0-Gamma*W_Q.                    (5)

Since q=B^N and B^u0 are both B modulo d*lambda, the three factors of
Gamma are units modulo every prime dividing d*lambda: rho is a power
of2, while the other two factors reduce to B^2-1 and Hctrl in the
displayed table. Hence gcd(Gamma,dN)=1.

For clarity the Boolean coverage proof is restated. Put C0=d*lambda.
The first T0 powers of B^kappa are exactly the residues
1+C0*z,0<=z<T0, modulo dN=C0*T0, by the accepted order and valuation
facts. Normalize any target by B^-2. Choose epsilon in{0,1} so that
subtracting epsilon*B leaves a nonzero residue modulo lambda. Its least
residue a0 modulo C0 satisfies1<=a0<C0<T0 and gcd(a0,T0)=1. Write the
remaining target as a0+C0*v. Solve

    a0*z0+a0*(a0-1)/2=v modulo T0.

The a0 distinct orbit coordinates z0,z0+1,...,z0+a0-1 modulo T0 give
that sum. Include B^3 exactly if epsilon=1. The corresponding positions
are a subset of (2), with no repetitions and the stated maximum M0.
Thus every residue modulo dN is W_Q for some Boolean subset Q.

Choose such a subset for

    W_Q=(R0-d*u0)*Gamma^-1 modulo dN.            (6)

Fix C=C_Q,F=F_Q,alpha=q-F-C,R=R(C,F). By (5)--(6),

    R=d*u0 modulo dN.                           (7)

This is the accepted actual-rank controller applied as an arithmetic
lemma to (3), not to a valid native tiling. It has not reused a canonical
word, packed rank or private witness from another tuple.

## 4. Positive outer inputs, phase and exact transport

Equation (4) gives positive F,C,alpha, with C=q-F-alpha. Consequently

    G=q(q-F)-C=q*alpha+(q-1)*C>=q,
    R>q*(q^2-1)>3q.

The mask term is positive. Since q=0 modulo4,J=1 modulo4,C=1 modulo4
and F=U*C=0 modulo4, the low residue is

    R=(-1)*(-1)+2=3 modulo4.                    (8)

Indeed DC=0 modulo4 and all other terms of U are also0 modulo4. This
phase conclusion is purely arithmetic and does not assume a high mask.

Put t=dN. Since t>=4, 2^t>2t; the bound above therefore gives
R>2t>t+d*u0, since u0<N. Together
with (7), it gives a positive integer v0 such that

    R-t=d*u0+t*v0.

Now set

    X=2^R, w=2^(R-t)=B^u0*q^v0,
    z=1+(w-B^u0)*C/(q-1), s=1, Y=q^3.          (9)

All these are positive integers. In particular w-B^u0 is a positive
multiple of q-1. Since F=(K+B^u0)C, substitution in the full transport
factor gives

    Nt=F+(w-B^u0)C+q-F
        -(q-1)-(w-B^u0)C=1.                    (10)

Thus all outer relations in section1 hold on their actual fixed ports.

## 5. The first norm and the deliberately oversized remainder

Set E=XY, a=E+Y=Y(X+1), A=a+2 and Delta=A^2-1. Put

    r=(R-1)/2, n=r+1=(R+1)/2,
    P0=2XY^2+1, k=2*psi_P0(n), tau=chi_P0(n).

Here chi_t(j),psi_t(j) are the integer Pell sequences with initial
pairs(1,0),(t,1). All these indices and values are positive. Since
P0=1 modulo E, their recurrence gives k=2n=R+1 modulo E. Hence

    h=(k-R-1)/E

is an integer. It is positive: n>=2, k>=4P0 and P0>R. We get Nk=1.
Writing b0=XY^2, ell=b0*k, the Pell norm at P0=2b0+1 gives exactly

    tau^2-ell*(ell+k)=1,                         (11)

so the **retained** first norm N0 is1; this is not an N0-deletion argument.

Set c=psi_A(R), and define eta=c-kY. The following elementary growth
proof shows eta>k. The Pell recurrence gives

    c>= (2A-1)^(2r), k<=2*(2P0)^r.

Also

    (2A-1)^2-2P0*X
      =4Y^2*(2X+1)+12Y*(X+1)+9-2X>0.

Therefore

    c/k>X^r/2.

Here r>=2 and R>3q. Since2^q>q+1 for q>=2, X=2^R>q^3+1=Y+1;
thus X^r/2>X>Y+1. It follows that

    eta=c-kY>k>0.                              (12)

The proposed input eta is positive, while the old input required to
restore k=eta+zeta would be zeta=k-eta<0. This is precisely the lost
strict interval: the old formula has kY<c<k(Y+1), whereas (12) puts
this construction strictly above its upper endpoint.

## 6. Positive main trace, gamma, and normalized strong witnesses

Let D*=chi_A(R). Set H=4a+3 and

    gamma=(D*-a*c-X)/H.

This is an integer. In the Pell identity modulo H one may replace
sqrt(Delta) by a because Delta=a^2+H. Thus

    chi_A(R)-a*psi_A(R)=(A-a)^R=2^R=X modulo H.

Moreover chi_A(R)=A*c-psi_A(R-1), so

    D*-a*c=2c-psi_A(R-1)>c>X.

The final inequality follows from R>=2 and c>=psi_A(2)=2A>X. Therefore
gamma>0, the supplied D in section1 equals D*, and N1=1.

Choose m=R*c and define

    f=chi_A(m), b=psi_A(m), i=b/c^2.

The quotient is a positive integer. Expand
(chi_A(R)+c*sqrt(Delta))^c: its first sqrt(Delta) coefficient contains
c*c, and every later odd term contains at least c^3. Thus c^2 divides
psi_A(R*c)=b. The Pell norm gives

    f^2-Delta*i^2*c^4=1,
    S=Delta*i*c^2=Delta*b,
    S^2=Delta*(f^2-1), Ns=Delta.                (13)

These are fresh symbolic witnesses, not copies from a compiler tuple.

## 7. Positive squared-modulus quotient T and auxiliary ordinate

The integer polynomials Q_j have

    Q_0(Z)=1, Q_1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)Q_j(Z)-Q_(j-1)(Z),
    chi_t(2j+1)=t*Q_j(t^2),
    Q_j(0)=(-1)^j*(2j+1),
    Q_j(1-A^2)=(-1)^j*psi_A(2j+1).

These full integer polynomial identities are the ones proved and used
in compact66 PROOF section4. With R=3 modulo4, define

    V*=chi_S(R)/S, y=psi_S(R),
    T=(V*+c+R*f^2)/(c*f^2).                     (14)

The odd-index identity makes V* a positive integer, and y is positive.
Since (R-1)/2 is odd, (13) and the Q identities give

    S^2=1-A^2 modulo f^2, V*=-c modulo f^2,
    c divides S, V*=-R modulo c.

Also f^2=1 modulo c and gcd(c,f)=1. Hence the numerator in (14) is
divisible by f^2 and by c, so T is an integer; it is strictly positive.
Its defining equality gives exactly the full proposed expression

    f^2*(c*T-R)-c=V*.

Finally the Pell identity at parameter S gives

    S^2*((V*)^2-y^2)+y^2=1.                    (15)

Thus the proposed input T is positive and Na=1, with no shifted
quotient, divisibility assumption on a former T, or sign premise for
an unknown auxiliary witness.

## 8. Complete factor check and scope of the obstruction

The construction supplies every one of the fifteen proposed inputs as
a positive integer. Equations(10)--(15) give

    N0=N1=Na=Nk=Nt=1, Ns=Delta>0,
    P_direct=1*1*1*1*1*Delta-Delta=0.

All four fixed integers are exactly the accepted indexed tuple, not
arbitrary ports. In particular this is stronger than an earlier
free-port illustration, which by itself could only refute a universal
local implication eta<k. The construction here uses only the accepted
actual-port controller facts and direct size bounds. It does not assume
that the fixed machine halts, nor start with any computation tableau.

The deliberately incomplete native cell at the origin selects Start0
but has zero copy/anchor bits. The aggregate complement lemma says it
fails the native clause mask: one selected tile requires its nonzero
41-bit payload, whereas those copies encode0. Safe dummy1063 positions
have coefficient0 in both clause bands and do not repair this origin
clause. Thus the counterfamily is not secretly a new native computation
certificate. The missing interval prevented the old half-binomial and
population recovery; the retained factors alone do not impose that mask.

Every genuine old positive witness still maps to the proposed formula
by taking its positive k=eta+zeta and discarding zeta. The reverse map
cannot be justified by deriving eta<k: (12) is an actual-port obstruction,
even when **every normalized unit is +1**. No early unit-sign shortcut
or deletion of N0 is involved.

This note proves an ordinary obstruction to this particular direct-k
proposal. It does not prove that every other65-operation architecture
fails, establish a general gate lower bound, alter the current equation's
ordinary proof, prove or refute Con(ZFC), or supply a Lean theorem. The
counterfamily is specified symbolically; no enormous witness integer or
new numerical tuple is materialized. Only this new note and inert
pins/manifest are written. No application/helper/AST/compiler/search,
Lean, TeX or PDF process is imported, compiled or run. The maintained
page, all existing source, coefficient data and frozen packages stay
unchanged. Independent ordinary reviews are still required.
