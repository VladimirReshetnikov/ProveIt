# The squared quotient does not repair a c-linear strong Pell constraint

This is a CODE-FREE ordinary obstruction proposed for independent review.
It extends the existing H10 linear-strength target construction from a
congruence modulo f to the maintained P66 quotient modulo f^2. It does
not supply a zero of a modified complete consistency equation. The
maintained radix55 equation with fifteen positive variables, 66 operations
and degree 157, its four constants,
all existing sources, and Lean remain unchanged.

The concrete conclusion is that replacing S=i*Delta*c^2 by S=i*Delta*c
admits positive **arithmetic-interface** witnesses with main Pell index
p different from the target R, even with

    V=f^2*(c*T-R)-c,
    0<R<c/2, c>A*Delta^2, m>2p, f>2c.

Thus the current index-recovery lemma does not transfer to that lower
degree chart. A proof using the remaining simultaneous source equations
might still exclude these witnesses. No such proof or full obstruction
is claimed here. No application, helper, import, AST, coefficient
collector, numerical Pell evaluation, Lean, TeX or PDF process was run.

## 1. The precise tempting source change

Use the complete current P66 abbreviations with fifteen positive inputs

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Treat beta,K0,MC,MF as the same four fixed ports as in the pinned
current radix55 source; MF is the once-shifted source mask. Define

    q=beta*J+1, C=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, ell=E*k*Y, c=k*Y+eta,
    a=E+Y, H=4a+3, Delta=a^2+H, D=X+a*c+gamma*H,
    R=[(q-1)*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    V=f^2*(c*T-R)-c,
    N0=tau^2-ell*(ell+k), N1=D^2-Delta*c^2,
    Nk=k-h*E-R, Nt=(K0+w)*C+(q-F)-z*(q-1).

The proposed change is only

    S_linear=i*Delta*c,
    Na_linear=S_linear^2*(V^2-y^2)+y^2,
    Ns_linear=Delta*f^2-S_linear^2,
    P_linear=N0*N1*Na_linear*Nk*Nt*Ns_linear-Delta.       (1)

This section specifies a counterfactual chart for analysis, not an
accepted candidate or a newly generated source/tuple/coefficient packet.

At the source level it has a same-cost schedule. In the pinned literal
parent replace exactly the three rows

    c2=c*c, Dc2=Delta*c2, normalized_S=i*Dc2

by

    Dc=Delta*c, Dc2=Dc*c, normalized_S=i*Dc.

The first two remain before N1 and the last remains in the auxiliary
block; every other row is unchanged. All three are multiplications.
Consequently the syntactic schedule still has 66 operations, namely
38 multiplications, 15 additions and 13 subtractions. This is a hand
schedule identity, not an executed or accepted finite result.

Every positive parent witness maps into (1) by i_linear=i_parent*c,
with every other input unchanged: S_linear then equals S_parent, and
all six factors and the entire output agree exactly. Restoring the same
parameters would require c|i_linear; this is not part of (1).

For completeness the hand degree calculation is exact, rather than an
endpoint claim. Put q0=beta*J, k0=eta+zeta and C1=q0-F-alpha. Here

    deg(c)=5, deg(Delta)=12, deg(V)=8, deg(S_linear)=18.

The only inherited leading cancellation is N1, whose exact degree 18
follows from Z=X+gamma*H and

    N1=2*a*c*Z+Z^2-H*c^2.

The complete factor degrees and homogeneous leaders are

| Factor | Degree | Leader |
| --- | ---: | --- |
| N0 |22| -w^2*k0^2*s^4*q0^14 |
| N1 |18| 8*w^2*k0*s^3*q0^11*gamma |
| Na_linear |52| i^2*w^4*k0^4*s^8*q0^28*f^4*T^2 |
| Nk |7| -h*w*s*q0^4 |
| Nt |2| w*C1-z*q0 |
| Ns_linear |36| -i^2*w^4*k0^2*s^6*q0^22 |

Their product has exact degree 137 and leader

    -8*q0^79*h*gamma*i^4*k0^9*w^13*s^22*T^2*f^4
       *(w*C1-z*q0).

The coefficient of
J^80*h*gamma*i^4*eta^9*w^13*s^22*T^2*f^4*z is 8*beta^80,
which is nonzero for positive beta. Subtracting Delta cannot cancel it.
The unproved part is the consistency calibration of this chart, not its
formal hand degree. No operation/degree frontier is promoted by it.

## 2. Pell conventions and a full squared-modulus period

For integers A>=2 and n>=0 define chi_A(n),psi_A(n) by

    (A+sqrt(Delta))^n=chi_A(n)+psi_A(n)*sqrt(Delta),
    Delta=A^2-1.

Equivalently both coordinates satisfy the recurrence
u_(n+1)=2*A*u_n-u_(n-1), with initial pairs (1,0),(A,1).
All uses below are ordinary integer polynomial identities in the formal
quadratic ring Z[t]/(t^2-Delta), so a congruence modulo an integer applies
to both coordinates. No square root is being evaluated numerically.

For every m>=1 put f=chi_A(m), b=psi_A(m). The Pell and doubling
identities give

    f^2-Delta*b^2=1,
    (A+t)^(2m)=(2f^2-1)+2f*b*t
                  =-1+2f*b*t modulo f^2.

Raise the last expression to the positive even exponent 2f. Every
binomial term of order at least 2 contains f^2. The constant term is 1,
and the linear term is -4f^2*b*t. Thus

    (A+t)^(4mf)=1 modulo f^2.                         (2)

In particular, for every u>=0 and p>=0,

    psi_A(p+4mf*u)=psi_A(p) modulo f^2.              (3)

This is the additional period needed for the maintained squared quotient.
The existing modulo-f target obstruction alone does not establish (3).

## 3. A general positive wrong-target interface family

Choose A>=3 and p>=3 with p=3 modulo4. Set c=psi_A(p) and suppose
gcd(p,c)=1. Choose a positive multiple m of p such that gcd(m,c)=1,
and put

    f=chi_A(m), b=psi_A(m), i=b/c, S=Delta*b.

The quotient i is a positive integer: writing d=chi_A(p), composition
gives psi_A(p*j)=c*psi_d(j). Also c is odd, since reducing the
recurrence modulo 2 gives psi_A(p) odd for every odd p. The Pell norm
implies gcd(f,c)=1 because c divides b. Therefore gcd(m*f,c)=1.

Let R be any positive integer congruent to p modulo4. Choose a
nonnegative integer u satisfying

    m*f*u=(R-p)/4 modulo c,

which is possible by the preceding unit property. Put

    nu=p+4*m*f*u, j=(nu-1)/2,
    Vstar=chi_S(nu)/S, y=psi_S(nu),
    T=(Vstar+c+R*f^2)/(c*f^2).                       (4)

The use of j here is a local polynomial index, unrelated to input J.
This CRT specifies symbolic witnesses; it is not a hidden fixed program
or a newly materialized integer constant in the consistency equation.
We now verify every division, equation and sign in (4).

First nu>=p>=3 and nu=p modulo4, so j is odd. Define integer
polynomials

    Q0(Z)=1, Q1(Z)=4Z-3,
    Q_(j+1)(Z)=(4Z-2)*Q_j(Z)-Q_(j-1)(Z).

The recurrence and initial values prove the full identities

    chi_t(2j+1)=t*Q_j(t^2),
    Q_j(0)=(-1)^j*(2j+1),
    Q_j(1-A^2)=(-1)^j*psi_A(2j+1).                 (5)

For the third identity the signed odd psi subsequence has recurrence
coefficient 2-4A^2 and initial values 1,1-4A^2, which agree with Q at
1-A^2. Thus Vstar=Q_j(S^2) is an integer, and it is positive because
S>=1 and the Pell sequence chi_S(nu) is positive. In fact S>=8c>1,
so the usual nondegenerate Pell identities apply. Also y>0.

The strong norm gives

    f^2-Delta*i^2*c^2=1,
    S=Delta*i*c, S^2=Delta*(f^2-1).                (6)

Consequently S^2=1-A^2 modulo f^2. By (3) and the odd sign in (5),

    Vstar=-psi_A(nu)=-c modulo f^2.               (7)

Since c divides S, (5) and the definition of u also give

    Vstar=-nu=-R modulo c.                       (8)

The norm gives f^2=1 modulo c. Hence the numerator defining T in (4)
is divisible both by f^2, using (7), and by c, using (8). As gcd(c,f)=1,
it is divisible by c*f^2. Its three summands are strictly positive,
so T is a strictly positive integer. Its definition is exactly

    Vstar=f^2*(c*T-R)-c.                          (9)

Finally the Pell norm at parameter S and index nu gives

    S^2*(Vstar^2-y^2)+y^2=1,
    Delta*f^2-S^2=Delta.                         (10)

Thus the entire current quotient formula and both proposed local norm
equations hold. In addition d=chi_A(p) supplies d^2-Delta*c^2=1.
The main Pell index is p. Whenever p!=R, these local equations do not
recover R as that index. Strict monotonicity of psi_A distinguishes them.

## 4. Explicit parameters retaining the ordinary local size margins

Take, without any Pell search or numerical materialization,

    A=28, Delta=783, p=7, R=11, n=6, m=28=4p,
    c=psi_28(7)=64*28^6-80*28^4+24*28^2-1,
    d=chi_28(7)=64*28^7-112*28^5+56*28^3-7*28,
    f2=2d^2-1,
    f=2*f2^2-1=chi_28(28), i=4*d*f2.

The doubling identity gives psi_28(28)=4*c*d*f2, so these are exactly
the f,i of Section 3. Reducing c's printed polynomial modulo 7 gives
c=-1 modulo7. It is odd; hence gcd(28,c)=1. Moreover
d^2=1 modulo c, f2=1 modulo c and f=1 modulo c. Thus the needed
unit gcd(m*f,c)=1 is proved without evaluating any large Pell integer.
Choose the unique u in 1..c-1 with 28*f*u=1 modulo c. This interval
exists because c>1 and the target residue 1 is nonzero. Then

    nu=7+112*f*u=11 modulo c,

exactly the R=11 instance of (4). Equations (6)--(10) therefore give a
complete positive arithmetic-interface witness, with every division
proved integral and with p=7 different from R=11.

The relevant growth margins also hold directly. Since 28>=2,

    c>44*28^6>28^5>28*(28^2-1)^2=A*Delta^2.

The first strict inequality follows by factoring 28^6 in the first two
terms of the displayed c polynomial:64-80/28^2>44, and its remaining
term 24*28^2-1 is positive. In particular c>2(R+2), c>m and
0<R<c/2. Here A>R+4, m>2p and b=i*c>c. Since Delta>4, (6)
also gives f>2b>2c. The preliminary first-index consequences hold:

    2n=R+1, n<p<2n, p>=(R-1)/2, R=3 modulo4.

These are numerical index inequalities only. They do not assert that
n=6 is a first Pell index at common computed X,Y.

The same-parameter parent restoration fails. The integers c,d and f2
are pairwise coprime where needed: d^2=1 modulo c and f2=1 modulo c.
Since c is odd, gcd(c,4*d*f2)=1. Thus c does not divide i, whereas
the parent S=i_parent*Delta*c^2 would require i_parent=i/c. This rules
out that restoration map, not every alternative whole-source proof.

## 5. Prior art, source boundary and remaining obligations

The H10 note `complete75_linear_strong87_target_crt.md` already proves
arbitrary targets for the c-linear normalized strong norm with
V=of-c=jc-R, imposing congruences modulo f and c. Its nearby-target
family R=p+4 already retains the preliminary n,p inequalities and the
same substantial local growth bounds. The earlier
`complete75_linear_strong87_obstruction.md` gives a related R=5p family.
Those facts are prior art, not new reductions or new obstructions here.

The different H10 note `pell_kernel_squared_congruence.md` strengthens
the free target modulus from c to c^2 in a weakened single-product
coefficient system; its congruence involving the strong Pell abscissa
remains modulo f. That is not the quotient formula in (9).

The new bounded extension here is the full f^2-period (2), its use in
(7), and the positive **current** quotient (9), together with the exact
same-cost prospective P66 chart and hand degree in Section 1. The
pinned `normalized-strong-auxiliary-index/README.md` proves the valid
current c^2 theorem: c^2|psi_A(m) forces p*c|m. In the present family
only c|psi_A(m) holds, and c does not divide m=28. The stronger
quotient congruence by itself does not restore that missing rank fact.

The constructed parameters do **not** impose simultaneously

    q=beta*J+1, X=w*q, Y=s*q^3, A=Y*(X+1)+2,
    c=(eta+zeta)*Y+eta, eta,zeta>0,
    D=X+(A-2)*c+gamma*(4A-5),

nor the actual first norm, its Nk relation, packed defining R, transport
factor or fixed-port/native/source calibration. In particular A=28
is an independent local parameter here, not the enormous computed A
of a full positive radix55 source assignment. No halting computation,
false syntactic refutation or whole zero of (1) is supplied. The target
freedom proves failure of this proposed local recovery implication;
it does not decide soundness of a complete modified equation.

To promote the 66/137 chart one would need a new soundness proof using
those additional simultaneous constraints, or a valid replacement
interface enforcing the lost rank divisibility at the charged cost.
To refute that whole chart one would instead need a positive witness
satisfying all those definitions on the actual current four ports.
Neither obligation is discharged by this note. No global gate lower
bound, optimality, equation.pdf gain or Lean formalization is claimed.

SOURCE_PINS.json identifies every direct ordinary source used here and
the immutable complete radix55 evidence manifest for context. These pins do
not claim a new replay or re-audit of that parent. MANIFEST.json closes
only this new two-payload, code-free note. All mathematical assertions
above are hand proofs; there are no new execution receipts.
