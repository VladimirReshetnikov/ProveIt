# First-index deletion: a noncircular bootstrap and exact defect reduction

This is the earlier reduction stage of the investigation. The remaining
integrality question identified here is subsequently resolved negatively
by FULL_COUNTERFAMILY.md, which completes every retained source factor.
Statements of what remained open below describe this intermediate stage.

Status: new proof reduction, not a sound deletion theorem, counterexample,
or operation-bound improvement. Independent mathematical review reports
PASS for this reduction; its separate report records the precise scope.

This note concerns exactly the normalized81 and ordinary82 candidates in
`scout.json`, fetched as inert source data from commit
`3f4a974a5ddf12c46302fc5d2edafc3730277923` of
VladimirReshetnikov/ProveIt. Their parents are the normalized85 and
ordinary86 auxiliary-quotient sources, respectively. Every numeral must
obey the entire inherited fixed compiler recipe. In particular, the port
MF is the shifted mask MF0+B-1; neither arbitrary masks nor signed inputs
are permitted. The ordinary input and all 17 supplied witnesses are
strictly positive integers. No saved arithmetic schedule is executed here.

## Result

At every full positive zero of either candidate, the retained equations
already force

    p=R, R=3 (mod 4), R/2<n<R,
    d=2n-R odd, 1<=d<=R-2<E,
    (k-R-1) mod E=d-1,
    (k-R-1)/E>0.

Here p and n are the genuine main and first Pell indices, respectively.
Thus the missing h is always a positive rational number. It is a positive
integer exactly when d=1. There is no other possible inverse coordinate.
In particular, positivity is no longer a separate open issue. The sole
unresolved first-index issue on the full candidate zero set is

    Does the retained arithmetic force d=1?

This proof uses no deleted index equation, no conclusion from a complete
parent zero, and no canonical-witness restriction. The input norm is
retained and its sign is used, but its finer arithmetic is not needed for
this reduction. That unused structure may still decide d=1.

## 1. Literal quantities, units, and outer bounds

Write

    q=(B-1)J+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=Y(X+1),
    A=a+2, Delta=A^2-1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    V=c(Tf-1)-Rf^2.

The literal code register A denotes Delta, not the Pell parameter A.
T is the supplied auxiliary_quotient; R is the paid r_lhs expression.
The six factors are first, main, input, auxiliary, transport, and strong.
Their product is one at a full zero. Therefore each is an integer unit.

The main and input norms cannot be -1 modulo4 because Delta is0 or3.
For the normalized strong factor, the same observation gives

    f^2-Delta*(ic^2)^2=1,
    Kaux=Delta^2*(ic^2)^2=Delta*(f^2-1).

For ordinary strong, its literal factor is
1+(ic^2)^2-Delta*(f^2-1). Modulo4 it cannot be -1: for Delta=0
it is1 plus a square, and for Delta=3 it is a sum of two squares.
Consequently

    (ic^2)^2=Delta*(f^2-1)=Kaux.

In both cases Kaux is an integer square, hence0 or1 modulo4. The
auxiliary factor Kaux*(V^2-y^2)+y^2 cannot be -1 modulo4.

The first norm is tau^2-u(u+1)k^2, u=XY^2>1. Its negative Pell
equation has no solution: if tau,k are positive and k minimal, then
uk<tau<(u+1/2)k, so 0<(2u+1)k-2tau<k. Multiplication by the
inverse norm-one unit 2u+1-2sqrt(u(u+1)) gives another negative-norm
integer pair with that smaller positive second coordinate. Taking the
absolute value of its nonzero first coordinate gives a contradiction.
Zero coordinates are impossible; signs can first be removed. Thus all
five norms are+1, and the remaining transport factor is also+1.

Put C=q-F-Z-alpha-2dx, using the literal port twice_cell_bits=2d.
The sheared transport is

    (Kconstant+w)C+1-F-(t-1)(q-1)=1,

where t=transport_quotient>0. Its trailing part is nonpositive and
Kconstant+w>=2; hence C>=0 and F+Z<q. In fact C>0, but it is not
needed. The retained compiler packing bounds, which use only these
inequalities and the actual fixed masks, give

    q>=16, X>=q, Y>=q^3,
    (2q-1)(q^2-1)<R<q^4-q^3,
    E>=q^4>R+q^3, a>R+2.

These are pre-decoding inequalities, not consequences of q being dyadic.
Their elementary derivation is in the pinned parent proof Section3:
G=q^2-Z-qF lies in [2q-1,q^2-q-1], and the shifted mask contribution
lies strictly between0 and(q-1)(1+2q).

## 2. Pell indices and the source-independent strict ratio

The least positive Pell unit for u(u+1) has coefficient2, since a
coefficient1 unit would require a square strictly between u^2 and
(u+1)^2. Its first coordinate is P=2u+1. Consequently

    tau=chi_P(n), k=2psi_P(n), n>=1, P=2XY^2+1.

The main root D is positive by its literal formula; hence

    D=chi_A(p), c=psi_A(p), p>=1.

Here chi,psi are the integer Pell sequences at parameter A>=2:
chi_A(0)=1, chi_A(1)=A; psi_A(0)=0, psi_A(1)=1; both obey
z(j+2)=2A*z(j+1)-z(j). The fundamental integer-coefficient unit is
A+sqrt(A^2-1): any smaller positive coefficient is impossible.

Both positive supplied ratio slacks give kY<c<k(Y+1). We have P>A.
If p<=n, parameter and index monotonicity give
c<=psi_A(n)<=psi_P(n)=k/2, impossible. Thus n<p.

Also Q=2A^2-1>P, since A^2>XY^2+1. Duplication gives

    psi_A(2n)=2A*psi_Q(n)>=2A*psi_P(n)=Ak>k(Y+1).

If p>=2n this contradicts the upper ratio. Therefore

    p/2<n<p.                                      (2.1)

No first-index congruence was used.

## 3. A new small-index exclusion: p>=6

Let z_j=chi_A(j)-a*psi_A(j). It starts z_0=1,z_1=2 and obeys the
same Pell recurrence. Since H=4a+3 is odd and4A-1=H+4, the powers2^j
satisfy this recurrence modulo H. Thus

    X=z_p mod H=2^p mod H.                         (3.1)

Always 0<X<H. Also H>=4*4096*17+3>32. If p<=5, then2^p<H,
so (3.1) is the exact equality X=2^p. As X>=16, the only cases are
(p,X)=(4,16) or(5,32). By(2.1), each has n>=3.

For every A>=2 and p>=2,
psi_A(p)<(2A)^(p-1). Also psi_P(n)>=(2P-1)^(n-1).
As A=Y(X+1)+2<Y(X+2) and n>=3, we have

    c<[2Y(X+2)]^(p-1),
    kY>=2(2P-1)^2Y>32X^2Y^5.

For p=4,X=16 this yields

    c/(kY)<18^3/(4*16^2*Y^2)<1.

For p=5,X=32 it yields

    c/(kY)<34^4/(2*32^2*Y)
           <=34^4/(2*32^2*4096)<1.

Both contradict c>kY. Therefore p>=6. In particular

    c>=psi_A(6)=32A^5-32A^3+6A>A*(A^2-1)^2,
    c>2p, c>2R.                                  (3.2)

The first strict inequality is immediate from
31A^5-30A^3+5A>0. The second follows from Pell growth at A>=2;
the third follows already from p>=3, c>=4A^2-1 and A>R+2.
This is the missing noncircular replacement for the deleted bootstrap.

## 4. Rank and positive auxiliary coordinate, separately in each source

Normalized: f^2-Delta*(ic^2)^2=1 directly gives
f=chi_A(m), ic^2=psi_A(m) for m>0. Strong divisibility of psi,
together with c=psi_A(p), gives p|m. Write m=pk, d0=chi_A(p).
The binomial expansion of(d0+c*sqrt(Delta))^k gives

    psi_A(pk)/c = k*d0^(k-1) (mod c).

Because c^2|psi_A(m) and gcd(d0,c)=1, c|k. In particular c|m,
m>=pc>2p. Set S=Delta*ic^2; then S^2=Kaux and c|S.

Ordinary: the retained equation is(ic^2)^2=Delta*(f^2-1).
Apply the generic relaxed-rank lemma with the now independently proved
c>A*Delta^2. It gives

    f=chi_A(m), ic^2=Delta*psi_A(m), p|m, c|m,
    m>=c>2p.

The lemma's full argument, including the possible smaller fundamental
unit, is recalled in Appendix A. Set S=ic^2; again S^2=Kaux and c|S.
Since p|m, c|psi_A(m), hence c^2|(f^2-1). Therefore in both sources

    o=cT-Rf,
    j=(V+R)/c=Tf-1-R(f^2-1)/c                     (4.1)

are integers. Normalized integrality also follows directly from its
strong equation. No positivity is assumed yet.

In normalized form f^2=1+Delta*i^2*c^4; in ordinary form
f^2=1+i^2*c^4/Delta. By(3.2), in either case

    f>2c, f^2>Delta+c,
    Kaux-Rf^2-c=(Delta-R)f^2-Delta-c>0.             (4.2)

The auxiliary norm is Kaux V^2-(Kaux-1)y^2=1, y>0. It excludes V=0.
If v=|V|>1, then v^2-1=(Kaux-1)(y^2-v^2)>0, so y>=v+1 and
v^2-1>=(Kaux-1)(2v+1), forcing v>=2Kaux-1.
But T>0 gives V>-Rf^2-c>-Kaux. This excludes the large negative
branch. V=+1 or-1 is also impossible since V=-c modulo f and f>2c,
c>2. Therefore V>0. Equation(4.1) then gives of=V+c>0 and
jc=V+R>0, so o,j are positive integers.

We have obtained, in both sources, without restoring a parent zero:

    S>1, S^2=Delta*(f^2-1), c|S,
    S^2(V^2-y^2)+y^2=1,
    V=of-c=jc-R>0,
    f=chi_A(m), c|m, m>2p,
    0<R<c/2, 0<p<c/2.                              (4.3)

## 5. Exact main-index recovery and parity

Ordinary Pell classification of(SV,y) gives
SV=chi_S(ell), y=psi_S(ell) with ell>0. As S divides chi_S(ell),
ell is odd (even chi indices equal+/-1 modulo S). Put ell=2v+1.
There are integer polynomials Q_v satisfying

    chi_Z(2v+1)=Z*Q_v(Z^2),
    Q_v(0)=(-1)^v(2v+1),
    Q_v(1-A^2)=(-1)^v psi_A(2v+1).

These follow from Q_0=1,Q_1=4T-3 and
Q_(v+2)=(4T-2)Q_(v+1)-Q_v. Thus V=Q_v(S^2).
Reducing modulo f, using S^2=1-A^2 and V=-c, squaring, and applying
chi_A(2j)=1+2Delta*psi_A(j)^2 gives

    chi_A(2ell)=chi_A(2p) mod chi_A(m).

The plus-sign chi step-down with0<2p<m gives

    ell=epsilon*p+2m*t, epsilon in{1,-1}, t integer. (5.1)

For completeness, chi_A(j+2m)=-chi_A(j) modulo chi_A(m), and
chi is even in j. Reducing to an index in[0,m], strict monotonicity
and2chi_A(m-1)<chi_A(m) rule out all representatives except
2ell=+/-2p modulo4m. This is integer division by2, not division
in an even residue ring.

Modulo c, V=(-1)^v ell and V=-R. Since c|m, (5.1) gives
R=+/-p modulo c. The strict bounds in(4.3) force

    p=R.                                           (5.2)

Equation(5.1), with ell odd, makes p odd. To retain the fixed-minus
parity, write p=2r+1. Addition formulas give
psi_A(ell)=epsilon*(-1)^t*c modulo f. The two unsquared minus
congruences imply, since c>2p and f>2c,

    r+m*t odd,
    r+(m+1)*t odd.

Subtracting makes t even, then r odd. Therefore R=p=3 modulo4.
This is the generic fixed-minus argument, now applied only after its
premises have been recovered without the deleted equation.

## 6. The exact remaining defect and positivity of the rational inverse

Put d=2n-R. Equations(2.1),(5.2) imply

    1<=d<=R-2<E, d odd.

Since P=1 modulo E, the psi recurrence gives psi_P(n)=n modulo E.
Hence k=2n modulo E and

    (k-R-1) mod E=d-1,                             (6.1)

with the least nonnegative remainder0<=d-1<=R-3<E.
Moreover n>R/2 and R>=6 imply n>=2, so

    k=2psi_P(n)>=4P=8XY^2+4>R+1,

using E>R and Y>=1. Thus the unique forced inverse

    h=(k-R-1)/E

is strictly positive as a rational number. It is an integer if and only
if d=1, equivalently2n=R+1. If that is proved for all full candidate
zeros, the scout's exact full-product identity immediately restores a
positive parent zero; if a full candidate zero has d>=3, it has a
genuine nonintegral inverse. Neither alternative has been established.

## 7. A genuinely scaled parity consequence

At a full candidate zero q is even. Indeed, if q were odd, then
J=(q-1)/(B-1) would be even since B is even. In the literal packing

    R=(q^2-Z-qF)(q^2-1)+(MC+q*MF)J

both summands would then be even, contradicting R=3 modulo4. Therefore
X=wq is even, and Y=sq^3 is divisible by8. This uses the actual packing
equation, not a premature claim that q is a power of two. It does not
force d=1: the separate SCALED_FAMILY.md constructs dyadically scaled
first/main examples with d>1, including the required scalar R bounds.

## Appendix A. Ordinary relaxed-rank lemma used in Section4

Let Delta=A^2-1, c=psi_A(p)>A*Delta^2, and Z=ic^2 satisfy
Z^2=Delta*(f^2-1). Write Delta=d0*s0^2, d0>1 squarefree. The least
positive integer-coefficient norm-one unit in Q(sqrt(d0)) is
F+y0*sqrt(d0), and every positive integer-coefficient solution is its
power: divide a putative solution by the largest smaller power to
contradict minimality. Thus A=chi_F(e), s0=y0*psi_F(e).
Put L=psi_F(e). Then Delta=(F^2-1)L^2, L<A, and
psi_F(ep)=Lc. The relaxed equation gives s0|Z and then
d0|(Z/s0); hence f^2-d0*(Z/(d0*s0))^2=1. For some b>0,

    f=chi_F(b), Z=(F^2-1)L*psi_F(b).

Put U=(F^2-1)L=Delta/L<=Delta, g=gcd(b,ep),
h=psi_F(g)=gcd(psi_F(b),psi_F(ep)). Strong divisibility is proved
by the addition identity and Euclid's algorithm, using coprimality of
chi and psi from their norm. Since c^2|Z,

    c*gcd(c,Delta)=gcd(c^2,U*psi_F(ep)) divides U*h,

so h>=c/Delta. If g<ep, it is a proper divisor, hence2g<=ep.
Duplication gives2h^2<psi_F(2g)<=Lc<Ac. But
h^2>=c^2/Delta^2>Ac, contradiction. Thus ep|b. Write b=em;
then p|m, f=chi_A(m), Z=Delta*psi_A(m).

Write m=pk. Expansion at chi_A(p)+c sqrt(Delta) gives
psi_A(pk)/c=k*chi_A(p)^(k-1) modulo c. The equation c^2|Z
therefore gives c|Delta*k. Let g0=gcd(c,Delta). The main expansion
modulo Delta gives gcd(c,Delta)=gcd(p,Delta), hence g0|p.
Thus c/g0|k and g0|p, proving c|pk=m. Finally m>=c>2p.

## Provenance and scope

Primary source links at the pinned commit:

- [Scout](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/first_index_quotient_deletion_scout.md)
- [Normalized85 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete85_auxiliary_bezout_projection.md)
- [Ordinary86 proof](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete86_ordinary_auxiliary_projection.md)
- [Relaxed-rank lemma](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md)
- [Fixed-minus parity](https://github.com/VladimirReshetnikov/ProveIt/blob/3f4a974a5ddf12c46302fc5d2edafc3730277923/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)

Exact authored checks and any subsystem search are recorded separately.
No universal zero is claimed materialized. The smallest established full
universal polynomial bound remains85.
