# A first-Pell carrier: uniform14-positive-variable,65-operation equation

This complete ordinary arithmetic proof removes one positive variable and
one integer-leaf operation from the accepted P66 front, lowering exact
degree157 to150. It applies to every retained native specialization that
satisfies the scalar boxes and canonical P66 completeness stated below.
In particular it applies to the complete low-padding2963 and doubled-
clause2953 tuples. Their four fixed integers and native arguments are
unchanged by this arithmetic transformation.

The idea is credited to the incoming archive
`docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip`, SHA256
`759b713ab7d3853f4fbd687439f25bada1a824e6b71da7dc0dec0516fca6e514`.
Its complete proof and literal graph were read as inert data. No incoming
Python, make target, verifier or build command was executed. Exact inert
copies accompany this proof as `INCOMING_PROOF.md` and
`INCOMING_CARRIER65.json`. The proof below independently states the full
uniform argument and explicitly transports it to the current coefficients;
it does not adopt the archive's different fixed tuple or seed decoder.

## 1. Exact polynomial and retained interface

Let beta,K,MC,MF be fixed positive integers satisfying

    beta>=31, K>0, 0<MC<beta<MF<2beta.                  (A)

Here MF is the source mask, already shifted by beta exactly once.
The fourteen independent variables, all strictly positive integers, are

    J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma.

Define polynomial abbreviations

    qminus=beta*J, q=qminus+1, C=q-F-alpha,
    X=wq, Y=sq^3, E=XY, k=eta+zeta,
    ell=EkY, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H, D=X+ac+gamma*H,
    R=[qminus*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    tau=E*n+k-R,
    V=f^2*(cT-R)-c, S=i*Delta*c^2,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Na=S^2*(V^2-y^2)+y^2,
    Nt=(K+w)C+(q-F)-z*qminus, Ns=Delta*f^2-S^2.

The single equation is the integer polynomial

    P65=N0*N1*Na*Nt*Ns-Delta=0.                       (B)

The parent P66 has positive independent h and tau instead of n, adds
`Nk=k-hE-R`, and multiplies Nk into the product in(B). Every other
abbreviation and all four ports are identical. The retained parent
interface consists of its ordinary soundness theorem and canonical
completeness: any positive parent zero yields a syntactic refutation;
a refutation supplies a positive parent zero with

    N0=N1=Na=Nk=Nt=1, Ns=Delta, R>0.                 (C)

We do not infer(C) from the parent product equation alone. Canonical
completeness is sufficient here; an all-zero parent sign theorem is
unnecessary for zero-existence equivalence.

## 2. Consecutive-product Pell arithmetic

Let m>=2 and D0=m(m+1). There is no integer solution of
`u^2-D0*v^2=-1`. For if one existed, take a solution of minimum positive
|v|, replace u,v by absolute values, and observe

    m*v<u<(m+1/2)*v.

The first inequality follows from `m*v^2>1`; the second follows from
D0<(m+1/2)^2. Multiplication by the integral norm-one unit
`(2m+1)-2*sqrt(D0)` produces another norm-minus-one solution, with
second coordinate `v'=(2m+1)v-2u` strictly between0 and v. Its first
coordinate may be replaced by its absolute value. This contradicts
minimality and proves the obstruction without a sign premise on u.

Every positive solution of `u^2-D0*v^2=1` is a positive power of
`(2m+1)+2*sqrt(D0)`. Indeed v=1 is impossible because
`m^2<D0+1<(m+1)^2`. For v>=2 the same multiplication gives

    0<=v'=(2m+1)v-2u<v,
    u'=(2m+1)u-2D0*v>0.

For the nonnegative inequality use
`u^2=D0*v^2+1<=(m+1/2)^2*v^2`; the strict upper inequality follows
from u>m*v. Positivity of u' follows from u>sqrt(D0)*v and
2m+1>2sqrt(D0). Descent terminates at(1,0). Reversing it proves
classification, including the least positive solution(2m+1,2).

Write P=2m+1 and define the usual integral Pell polynomials by

    chi_P(r)+psi_P(r)*sqrt(P^2-1)
       =(P+sqrt(P^2-1))^r.

Then every positive solution has
`u=chi_P(r), v=2psi_P(r)` for r>=1. If E divides m, then P=1 modE;
the recurrence chi_0=1, chi_1=P and
`chi_(r+1)=2P*chi_r-chi_(r-1)` proves `u=1 modE`.
At r=1, v=2. At r>=2,
`v>=2psi_P(2)=4P`. Also u>v because D0>1. These statements are
elementary integer identities and finite descent, formalizable in ZFC.

## 3. Recover all signs before bounding the new carrier

On a positive assignment satisfying(B), q>=32 and X,Y,E,a are positive.
Since Delta=(a+2)^2-1>0 and

    Ns=Delta*(f^2-Delta*i^2*c^4),

integer cancellation of Delta gives

    N0*N1*Na*Nt*(f^2-Delta*i^2*c^4)=1.

Every factor is therefore an integer unit. To exclude N0=-1, put
m=EY>=2 and note `ell(ell+k)=m(m+1)k^2`. Section2 applies even if
tau was negative or zero; no positivity of this abbreviation has yet
been used. For N1 and the normalized strong factor, Delta is0 or3
modulo4, and a square minus Delta times a square cannot be3 modulo4.
For Na, S squared is0 or1 modulo4, making Na congruent to y squared
or V squared respectively. Thus these four norm factors cannot be-1.
The remaining factor Nt must be1. Consequently

    N0=N1=Na=Nt=1, f^2-Delta*i^2*c^4=1, Ns=Delta.    (D)

This conclusion has not used a native interpretation, an index quotient,
a sign of tau or C, or any bound on R.

## 4. Scalar recovery and a positive omitted quotient

If C<=0, Nt=1 would imply

    1=Nt <= (q-1)-z(q-1) <=0,

because K+w>0 and F,z>=1. Hence C>0. Put u=q-F=C+alpha. Then
`2<=u<=q-1` and `1<=alpha<=u-1`. Thus

    2q-1 <= G=(q-1)u+alpha <= q^2-q-1.

By(A) and beta*J=q-1,
`0<(MC+qMF)J<(1+2q)(q-1)`. The actual rank therefore satisfies

    q(q^2-1)<R
      <(q^2-q-1)(q^2-1)+(1+2q)(q-1)=q^4-q^3.

In particular R>1 and R+2<E, because E=wsq^4>=q^4. Positivity of
n now gives `tau=En+k-R>=E+k-R>k+2>0`. This order of reasoning is
essential: tau's positivity follows from(D), rather than justifying(D).

Apply section2 to N0=1 with m=EY. The positive pair(tau,k) satisfies
`tau=1 modE`, so the defining tau relation implies
`E|(k-R-1)`. Let

    h=(k-R-1)/E.

This is an integer. Since k>0 and R+1<E, h>-1, hence h>=0. If h=0,
then k=R+1<E. At Pell index r=1, k=2 would force R=1, contradicting
the rank lower bound. At r>=2, k>=4(2EY+1)>E, again a contradiction.
Therefore h>0 and `Nk=k-hE-R=1`.

Keep all supplied variables other than n, restore the positive independent
tau=En+k-R and h above, and retain all four ports. Every old norm and
transport factor has the same value as in(D), with the restored Nk=1.
The parent P66 equation is therefore exactly zero. This is an explicit
map from every positive new zero to a positive parent zero.

## 5. Canonical completeness and precise witness-map scope

Start with a canonical positive P66 zero supplied by(C). Its positive
first Pell root obeys tau=1 modE and tau>k by section2. The old Nk=1
gives k-R=1 modE. Therefore

    n=(tau-k+R)/E

is an integer and is strictly positive, because R>0. Keep the other
thirteen surviving inputs and delete old h,tau. The new abbreviation
En+k-R equals the old tau exactly. All remaining factors retain their
canonical values, so(B) vanishes.

These two maps prove zero-existence equivalence using only parent
soundness and canonical completeness. If one separately invokes the
retained all-zero parent sign/recovery theorem, the same formulas are
inverse on the entire positive zero sets: Nk=1 restores the original h,
and the defining carrier restores the original tau and n. That stronger
bijection is not needed for, and is not silently assumed by, the present
consistency equivalence. No division of an arbitrary ambient assignment
is performed; integrality is proved on the relevant zero sets.

## 6. Literal integer-leaf cost and exact degree

The complete data-only graph is `INCOMING_CARRIER65.json`. Relative to
the accepted66-row graph, remove hE, index_partial, Nk and the output
multiplication by Nk. Insert En=E*n, tau_partial=En+k and
tau=tau_partial-R, moving the first norm after the producer of R.
The resulting graph has65 live binary operations:37 multiplications,
16 additions and12 subtractions. Its leaves are integer numerals,
the fourteen positive inputs and the four fixed integer ports; there
are no rational leaves or implicit divisions.

Give variables degree1 and fixed ports degree0. Tau has degree7, while
ell has degree11, so N0 has degree22. For the only nontrivial apparent
leading cancellation, put Z=X+gamma*H. Exact expansion gives

    N1=Z^2+2acZ-Hc^2,

of degree18: its degree18 contribution is from2ac*gamma*H and cannot
cancel with the other terms. The remaining degrees are62,2,46 for
Na,Nt,Ns. With q0=beta*J and k0=eta+zeta, the complete highest
homogeneous form of P65 is

    8*q0^87*gamma*i^4*k0^13*w^12*s^25*T^2*f^4
       *(w*(q0-F-alpha)-z*q0).

Its coefficient at
`J^88*gamma*i^4*eta^13*w^12*s^25*T^2*f^4*z` is
`-8*beta^88`, nonzero for the actual positive beta. The exact degree
is150 for every retained specialization, not merely for generic ports.
The separate newly authored audit checks all graph rows, integer leaves,
topology, complete liveness, every retained-parent row and the entire
leading homogeneous polynomial. Its finite diagnostics do not replace
the unbounded arguments above.

## 7. Application to both complete current native tuples

For low-padding2963, the complete ordinary source is
`../low-padding-independent/PROOF.md`, SHA256
`ad952c6f1717a69e6b489e8c7af0bb52ce09414b78cc994b892b6e7f996d06f6`.
Its final finite certificate is
`d165186ba400ebc2074716d2e1a142505b93c6d150b3f1fc44e574e9664ca039`.
Its four ports total69,685 minimal unsigned bytes. Section4 supplies(A),
and section12 supplies the parent soundness and canonical completeness(C).
Hence this exact tuple may use(B) directly; no constant, field, physical
mask, native witness, controller prime or seed changes.

For scaled-clause2953 the complete ordinary source is
`../scaled-clause-independent/PROOF.md`, SHA256
`602b9560017f52835d36de8c1969ec8348381c8dae31876cb86905c5de2cdebe`.
Its final finite certificate is
`957faf013a17c2e8e04c03be166d903263d2aadaccac604d31f0791e005776ed`.
Its four ports total69,449 bytes. Sections4 and12 provide exactly the
same required interface, including the canonical unit signs, R>0 and
all-positive witnesses. Its changed native proof is independently
required and is not bypassed by this uniform front transformation.

Composing sections3..5 with either complete retained native and syntactic-
refutation calibration proves in ZFC that(B) has no positive integer
zero exactly when Con(ZFC), with the same syntactic consistency predicate.
Neither consistency nor inconsistency is assumed. This is an ordinary
proof with explicitly retained arithmetic, full-language and foundational
contracts; it is not a newly replayed end-to-end formal-kernel proof,
an actual unsolvability result, or a global minimality claim.

The incoming archive's399-character decoder is a separate proposed exact
identity and is not used here. Printed page layout, bindings and rendering
also require their own whole-source verification. The author of this
independent proof is `/root/complemented47_review`; ROOT coordinates
independent review and any later candidate promotion.
