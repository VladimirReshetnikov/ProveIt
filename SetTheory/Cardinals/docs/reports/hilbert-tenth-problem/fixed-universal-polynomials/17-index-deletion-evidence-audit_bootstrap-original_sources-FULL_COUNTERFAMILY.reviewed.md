# Full first-index-deletion collapse: a symbolic positive counterfamily

Status: author proof complete; root and independent mathematical review
have found no blocker, with the separate audit recording final status. This is a
mathematical witness construction, not execution of a saved compiler
schedule and not materialization of the astronomical Pell witnesses.

## Claim and exact scope

Fix ANY genuine admissible six-numeral compiler instance for the pinned
normalized85 or ordinary86 parent, and ANY ordinary positive input x.
Then its corresponding first-index-deleted candidate (normalized81 or
ordinary82) has a full strictly positive integer zero. The construction
preserves that exact fixed numeral tuple and the ordinary input.

Every constructed zero has a nonintegral forced inverse

    h=(k-R-1)/E,

with a strictly positive nonzero remainder. Thus it is a full-source
counterexample to the proposed positive zero-set restoration. Applied
to the compiler of the empty computably enumerable set, this also
disproves the claimed universal ordinary-input projection if one were
to assert it for the deleted candidate. No new operation bound follows.

The proof uses only the authentic contract, notably

    B=2^d>=16, ell=2d, b=inner_bits positive odd,
    K=Kconstant>0,
    MC=2 mod4, MF=MF0+B-1,
    0<MC,MF0<B-1,

and otherwise leaves all fixed program details untouched. MF throughout
is the literal shifted source numeral. Any further actual compiler
restrictions remain satisfied because the constants are not chosen or
changed here. These hypotheses are those in the pinned parent proofs.

All mathematical divisions and exponentiations below only define
existential witnesses. They are not extra source instructions.

## 1. A factorial radix with controlled residue exponent

Let the prescribed input index and word be

    I=ell*x+b, W=2^I.

Choose an integer L at least max(1100d,16,K,W,ell*x), and put

    t=L!, N=t/d, q=2^t=B^N, J=(q-1)/(B-1),
    t=2^a m with m odd,
    Q=q^2-1, M=(MC+q*MF)J.

Here 1100d divides t, hence N is a positive multiple of1100; t>=64
and a>=4. Also K,W,ell*x<=t. All these choices are finite integers.

We have q=1 modulo m. Indeed, for every odd prime power r^v dividing
t=L!, the two coprime numbers r^(v-1) and r-1 separately divide L!:
the first by its valuation, the second since r<=L. Therefore
phi(r^v)=r^(v-1)(r-1) divides t. Euler's theorem gives2^t=1
modulo r^v. Chinese remaindering over the odd prime powers proves
q=1 modulo m. In particular Q=0 modulo m.

Select the unique e among the four representatives e0,e0+m,e0+2m,
e0+3m, where0<=e0<m and e0=M modulo m, for which e=3 modulo4.
Because m is odd such an e exists, and

    3<=e<4m<=t/4.                                  (1)

Let Z be the least strictly positive integer congruent to e-M modulo
2^a. Then1<=Z<=2^a<=t. Since q=0 modulo4 and J=1 modulo4,
M=MC=2 modulo4, so Z=1 modulo4. Define

    C=W+Z,
    F=(K+2^e)C,
    alpha=q-F-2Z-W-ell*x,
    R=(q^2-Z-qF)Q+M.                               (2)

The retained source then computes marked_rhs=C and its W register=W.

## 2. All outer margins are strictly positive

We have C<=2t and, from(1),

    F<=2t(t+2^(t/4)),
    2Z+W+ell*x<=4t.

For t>=64,

    2t^2+2t*2^(t/4)+4t<2^t=q.                     (3)

For a direct elementary bound, t<=2^(t/8) for t>=64. Hence
2t^2+4t<=4t^2<=2^(t/2), and
2t*2^(t/4)<=2^(t/2). Their sum is at most2^(t/2+1)<2^t.
Thus alpha>0, and F,Z,C are also positive. In particular F+Z<q.
The genuine shifted-mask estimates therefore give exactly the parent
pretyping interval

    (2q-1)(q^2-1)<R<q^4-q^3.                       (4)

For completeness, G=q^2-Z-qF lies between2q-1 andq^2-q-1;
0<M<(q-1)(1+2q). These bounds imply(4). Thus R>q>t and R>5t+5.
The last comparison uses2^t>5t+5 for t>=64, proved at64 and preserved
when t increases by1 because2(5t+5)>5(t+1)+5.

## 3. The packed R satisfies both required arithmetic conditions

Modulo m, Q=0 gives R=M=e. Modulo2^a, q=0 and Q=-1 give

    R=Z+M=e.

As t=2^a m, this proves

    R=e modulo t.                                  (5)

Next, B^20=1 modulo55, because B=2^d and2^20=1 modulo55.
The geometric sum J has N terms and N is a multiple of1100=55*20.
Group it into N/20 blocks of20 terms. All blocks have the same
residue modulo55, and their number is divisible by55. Hence J=0
modulo55. Also q=B^N=1 modulo55, so Q=0 modulo55. Thus

    55 divides M,Q,R.

Finally(5), a>=4, and e=3 modulo4 give R=3 modulo4. Set

    u=R/55.

Then u is a strictly positive integer with u=1 modulo4. This u is
the obstruction-family parameter, not the input index I.

## 4. A dyadic first/main family at this exact packed R

Define

    p=R=55u, n=40u, defect=2n-p=25u,
    X=2^p, Y=2^(33u-1),
    w=X/q, s=Y/q^3,
    E=XY, a0=Y(X+1), A=a0+2, Delta=A^2-1,
    H=4a0+3, P=2XY^2+1,
    D=chi_A(p), c=psi_A(p),
    tau=chi_P(n), k=2psi_P(n).

We use a0 for the source quantity a, to distinguish it from the
2-adic valuation a of t. By(4), p>t, so w=2^(p-t)>0 is an integer.
Also p>5t+5 implies33u-1=3p/5-1>3t, so s>0 is an integer.
Thus the literal asymmetric scales X=wq and Y=sq^3 hold.

Both Pell norms hold by their definitions. We now prove the strict
ratio, rather than approximating it. Put L0=2XY, M0=4XY^2.
The chosen exponents satisfy

    L0^(p-1)/(2M0^(n-1))=Y.                        (6)

Indeed p=55u,n=40u,log2 Y=33u-1 make the powers on both sides equal.
Also

    2A-1=L0(1+1/X+3/(2XY)),
    2A=L0(1+1/X+2/(XY)),
    2P=M0(1+1/(2XY^2)), 2P-1>M0.

The bounds(2A-1)^(p-1)<=psi_A(p)<(2A)^(p-1), and the analogous
bounds at P, give

    c/(kY)>= (1+1/X+3/(2XY))^(p-1)
              /(1+1/(2XY^2))^(n-1)>1.

The strict inequality holds because the numerator's base exceeds the
denominator's base (Y>=1), and p-1>n-1. Thus c/k>Y. For the upper
bound, epsilon=1/X+2/(XY)<2/X. Since p>=55, we have
2p/2^p<1/2 (already true at p=4 and decreasing for p>=2), hence
(p-1)epsilon<1/2. The upper Pell bounds and(6) now give

    c/k-Y<4p*Y/X=110u*2^(-22u)<1.                  (7)

The last inequality holds at u=1 and decreases thereafter; or use
u<=2^(u-1). The binomial bound used here is
(1+epsilon)^j<=1/(1-j epsilon)<1+2j epsilon for0<j epsilon<1/2.
Consequently

    eta=c-kY>0, zeta=k-eta>0,

and k=eta+zeta,c=kY+eta exactly, as required by the literal source.

## 5. Complete the input norm and the shared rho/sigma split

Let z_j=chi_A(j)-a0 psi_A(j). It obeys the Pell recurrence and
z_0=1,z_1=2, and satisfies z_j=2^j modulo H. Thus

    gamma=(z_p-X)/H

is an integer. Define the input Pell coordinates and supplied quotients

    kappa=psi_A(I), mu=chi_A(I),
    delta=(kappa-I)/Delta,
    rho=(z_I-W)/H,
    sigma=gamma-rho.

Because I=ell*x+b is odd, the doubled-step recurrence gives
psi_A(I)=I modulo Delta. As I>=3 and A>=2, psi_A(I)>I, hence
delta is a strictly positive integer. The projection recurrence gives
integer rho. Since W<q<X<a0 and
z_I>psi_A(I)>=psi_A(3)=4A^2-1>W+H,
rho is strictly positive.

We also have I<t<p: W=2^I<=t and t<p. The positive sequence z_j
satisfies z_(j+1)>(2A-1)z_j for j>=1. Therefore

    z_p-z_I>=z_p-z_(p-1)>(2A-2)z_(p-1)>X.

It follows that

    sigma=(z_p-z_I-X+W)/H>0.

Both quotients are thus positive integers and the literal source
relations are exactly

    D=X+a0*c+(rho+sigma)H,
    kappa=I+delta*Delta,
    mu=W+a0*kappa+rho*H,
    mu^2-Delta*kappa^2=1.

This checks the actual input norm and its common rho coordinate; it
does not replace the input by a separate exponent witness or alter x.

An independent and simpler positivity verification uses
g_j=(z_j-2^j)/H. Its exact recurrence is

    g_0=g_1=0, g_2=1,
    g_(j+2)=2A*g_(j+1)-g_j+2^j.

It proves g_j strictly increasing for j>=1. Thus rho=g_I>0 and
sigma=g_p-g_I>0 directly because p>I>=3. This independently verifies
the shared-coordinate argument without a size approximation.

## 6. Complete the actual positive transport quotient

From(5), p=R=e modulo t. Since q=2^t and w=2^(p-t),

    w=2^e modulo(q-1).

Moreover p>5t+5 and e<t/4 imply p-t>e, hence w>2^e. Therefore

    transport_quotient=1+C*(w-2^e)/(q-1)

is a strictly positive integer. With F=(K+2^e)C, direct substitution
gives the literal sheared transport factor

    (K+w)C+q-F-transport_quotient*(q-1)=1.

No sign relaxation, raw-mask substitution or signed quotient was used.

## 7. Complete the auxiliary quotient for both actual source modes

This is the standard positive minus family, now at the constructed
exact p=R=3 modulo4. Put

    m_aux=2cp,
    f=chi_A(m_aux), iN=psi_A(m_aux)/c^2,
    S=Delta*psi_A(m_aux),
    y_aux=psi_S(p), V=chi_S(p)/S,
    o=(V+c)/f, j=(V+p)/c,
    T=(o+pf)/c.

All displayed quotients are positive integers, as follows. Expanding
(chi_A(p)+c sqrt(Delta))^(2c) shows c^2|psi_A(m_aux), so iN>0
is integral. Also S>c^2 and

    S^2=Delta*(f^2-1).

For p odd, the integer polynomial Q_((p-1)/2) satisfies
V=Q_((p-1)/2)(S^2). Since p=3 modulo4, its two reductions give

    V=-c modulo f, V=-p modulo c.

Here S^2=1-A^2 modulo f and S=0 modulo c. Thus o,j are integers.
Pell growth gives V>=chi_S(3)/S=4S^2-3>c>p, so o,j>0.
Moreover f^2=1 modulo c and of+p=c(j+1); multiplying modulo c
by f proves c|(o+pf), hence T is a positive integer. Finally

    c(Tf-1)-Rf^2=of-c=V,
    S^2(V^2-y_aux^2)+y_aux^2=1.                    (8)

In the normalized candidate supply i=iN. Its strong norm is
f^2-Delta*(ic^2)^2=1 and its literal auxiliary coefficient is
Delta^2*(ic^2)^2=S^2. Thus(8) is its exact retained auxiliary factor.

In the ordinary candidate supply i=Delta*iN. Then
(ic^2)^2=Delta*(f^2-1)=S^2; its literal strong factor is
1+(ic^2)^2-Delta*(f^2-1)=1, and its auxiliary coefficient is again
S^2. The same supplied T,f,y_aux and the same V satisfy(8).

The supplied quotient is T=auxiliary_quotient, not o or j. Those two
quantities are only convenient mathematical intermediates establishing
its positive integrality. Their construction introduces no extra
witness port and does not use h.

## 8. Full source zero and the nonintegral deleted coordinate

The constructed seventeen positive supplied coordinates, in exact order,
are

    J,F,alpha,transport_quotient,f,i,T,s,w,tau,
    eta,zeta,y_aux,Z,delta,rho,sigma.

All fixed numerals and the prescribed x are unchanged. The literal
computed quantities match those in Sections1–7. Each of the six
surviving factors is exactly+1, so the fully paid candidate product
minus1 is exactly zero, in either source mode.

Since P=1 modulo E, k=2n modulo E. Here p=R=55u,n=40u, so

    (k-R-1) mod E=25u-1>0.                         (9)

This is the least positive remainder because E=XY>25u. Also k>R+1,
so the forced quotient h is positive rational but not integral.
The exact scout identity

    Fparent+1=(Fcandidate+1)(k-hE-R)

therefore cannot restore any positive integer h at this retained tuple.

The construction proves more than a scaled subsystem example: the
actual paid R, transport and ordinary-input factors, shared rho split,
both ratio slacks, and the complete auxiliary quotient all hold with
the same witnesses and arbitrary authentic compiler numerals.

## Evidence boundary and review request

The infinite construction above is the evidence for a full positive
zero. It intentionally does not materialize factorial-radix/Pell
integers or evaluate a saved arithmetic schedule. Newly authored checks
may test its bounded number-theoretic identities and modest subsystem
fixtures, but those tests alone are not a full-source counterexample.

Independent reviewers should attack: the factorial totient divisibility;
e and Z CRT choices; shifted-M packing; the uniform outer margin;
source order and positivity in the input rho/sigma split; canonical T
integrality in both modes; and the final exact nonzero remainder.

## Relationship to the subsequent upstream scaled obstruction

The primary note
[first_index_scaled_obstruction.md](https://github.com/VladimirReshetnikov/ProveIt/blob/93c34e817c7bf726becd47326d22ec5e511a4251/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/first_index_scaled_obstruction.md)
at commit93c34e817c7bf726becd47326d22ec5e511a4251 proves an earlier
scaled first/main subsystem family, with necessary-mask packing examples.
It explicitly leaves input and auxiliary constraints uncompleted. Its
small p=55,n=40,X=2^55,Y=2^32 fixture also matches our independently
reproduced small fixture. That local fixture is context, not the claimed
advance here. This note's additional result is the uniform factorial-CRT
completion of the exact paid packing, genuine fixed compiler interface,
transport, ordinary input/shared rho, and both auxiliary quotient modes.
No checker or saved arithmetic schedule from that upstream note was run.
