# Retaining selected roots: degree414,218,124

## Completed literal forms

All unknowns are unrestricted integers and all coefficient leaves are the same
six fixed numerals as `PROOF.md`. These equations use the same source calibration.

| Variables | Retained roots | Exact degree | Binary operations |
|---:|---|---:|---:|
|13|none|1072|195|
|14|strong root f|414|148|
|15|f and positivity root g|218|130|
|16|f,g, and first Pell root tau|124|118|

The 14-variable degree414 point improves degree and operations over the incoming
degree652/230 fixed-prime point and degree696/150 root-fusion point. The separate
degree792/137 point remains a cost tradeoff. The 15-variable degree218/130 point
trades four degrees against nine operations compared with degree214/139. The
16-variable point improves degree184/135 in both measures. These are comparisons
to the inspected incoming packages, not global-optimality or priority claims.

The old exploratory retained-tau degree558 graph is dominated by the retained-f
construction and is not part of this release family.

## Common definitions

Retain all native definitions and the guard N,S of `PROOF.md`. In particular

    I=(2r+1)c^2, Df=1+Delta*I^2,
    Dtau=1+u(u+1)k^2, u=XY^2,
    Dmain=1+Delta*c^2,
    S=24N-21-(6p2-1)^2-(6p3-1)^2,
    M=2q^2, U=MH, b0=X+ac.

Now f is a new independent integer. Replace Q and V by the lower-degree
expressions

    Q=Delta*(f^2-1), delta=Q-1,
    V=f^2(cT-R)-c, Cy=QV^2-1,
    p=U(n+V)+M*b0+H(v-q^2).

Let

    Ff=f^2-Delta*I^2 = 1+(f^2-Df).

If a guard root g is retained, let

    Fg=g^2+22+(6p2-1)^2+(6p3-1)^2-24N = 1+(g^2-S).

If a first Pell root tau is retained, let

    Ft=tau^2-u(u+1)k^2 = 1+(tau^2-Dtau).

These simplified factors save literal arithmetic operations by canceling the
constant1 in the corresponding Pell radicand. The graph emits the factors in
the forms displayed above; the residual formulations are identical polynomials.

The weighted radicands needed below are

    A=M^2 Dmain,
    B=9U^2 Dtau,
    Cn=U^2 Cy,
    D=81U^2 S.

Use the same universal sign-product polynomial F_r on r radicands. The three
centered cleared norms are

    N4=delta^8 F_4(p;A,B,D,Cn/delta),
    N3=delta^4 F_3(p;A,B,Cn/delta),
    N2=delta^2 F_2(p;A,Cn/delta).

The denominators clear identically. In particular the last norm has the short
ordinary expression

    N2 = [delta*(p^2-A)-Cn]^2 - 4*delta*A*Cn.

The completed equations are

    P14=(1+N4)*Ff-1 = 0,
    P15=(1+N3)*Ff*Fg-1 = 0,
    P16=(1+N2)*Ff*Fg*Ft-1 = 0.

The added variables are respectively f; f,g; and f,g,tau. No other abbreviation
adds a quantified variable. The graph builder supplies literal division-free
two-,three-,and four-root norm evaluations.

## Unit-product recovery, without a sign assumption

On every integer assignment, q is even and W is a multiple of4, so X is a
multiple of8. Also a=(X+1)Y is even because Y=qv. Hence

    Delta=3 mod4,
    Df=1+3I^2=0 or1 mod4,
    Dtau=1 mod4,
    S=1 mod4.

The last congruence uses that each 6pi-1 is odd. It follows that

    Ff = f^2+I^2 mod4 is0,1,or2,
    Fg = g^2 mod4 is0 or1,
    Ft = tau^2 mod4 is0 or1.

None can equal -1. Meanwhile M=2q^2 is divisible by8, as is U. All integral
weighted radicands and the rational radicand's numerator Cn are therefore
divisible by64. Every nonleading monomial of the cleared norm contains one
such factor. For r=2,3,4,

    Nr = delta^(2^(r-1))*p^(2^r) mod4 is0 or1.

This assertion does not require delta to be odd: its exponent is even. Thus
1+Nr cannot be -1 either.

A product of integers equals1 only if every factor is1 or-1. Since -1 has
been excluded for every factor, each polynomial equation is equivalent to
all its displayed factors being1. In particular it forces the norm to vanish
and f^2=Df; when present, it forces g^2=S and tau^2=Dtau. This argument
precedes interpreting any radical or dividing by delta.

## Soundness and completeness

The unconditional mod3 identities in `PROOF.md` remain valid: Delta=0 mod3,
Q=0 mod3, delta=-1 mod3, Cy=-1 mod3, Dtau=Dmain=S=1 mod3. In particular
delta never vanishes even before f^2=Df is known. Let e=v_3(H)>=1. The
remaining radicands have pairwise distinct even valuations:

    A:0, Cn/delta:2e, B:2e+2, D:2e+4,

omitting whichever radicands have retained roots. The valuation lemma recovers
every nonretained root rationally. The unit factors restore the retained ones.
Thus we obtain integer main, first Pell, and guard roots; the auxiliary root
is rational at this stage.

The guard root, whether recovered or retained, gives N>0 and then G>0 and
eta*zeta>0. This excludes c=0 exactly as in `PROOF.md`. The strong factor now
gives Q=Delta*(f^2-1)=Delta^2*I^2>1, so rational auxiliary descent makes its
root y integral. The same carrier congruences restore

    v=q^2(2v_old+1),  gamma=(d-b0)/H in Z.

The strong and quotient restoration maps are unchanged. Consequently every
new zero restores the normalized source Cal.

Conversely take a canonical Cal witness and its integral roots. Retain f and
any indicated roots g,tau. Choose the generalized pentagonal representation
of positive N as before. The free n can be chosen by

    n=gamma+y-V-(v-q^2)/M
         +3*tau if tau is not retained
         +9*g   if g is not retained.

All additions are integral. This makes one factor of the appropriate norm
vanish; each retained unit factor equals1. Hence the corresponding P vanishes.

These are exact two-way maps. They do not assume the new variables are positive
or that every old root has a prescribed sign. Sign choices are absorbed in the
signed roots; n is unrestricted. They compose with exactly the same inherited
ordinary source/native/refutation theorem as the 13-variable form.

## Degree bounds and exact leading coefficients

Use subscript0 for leading homogeneous parts. The native definitions have

    q0=6 beta*j, W0=12w, Y0=q0*v, X0=q0*W0,
    a0=X0*Y0, i0=2r,
    R0=-q0^3(W0*C-q0*z), k0=R0+h*a0,
    U0=8q0^2*a0, M0=2q0^2,
    S0=-24Y0^4*k0^4,
    Dt0=X0^2*Y0^4*k0^2,
    Q0=a0^2*f^2, V0=-f^2*R0.

The degrees now are Q,delta:10; V:7; Cy:24; p:13; A:14; B:34; D:40;
Cn:36. The retained unit factors have degrees14,28,22 for Ff,Fg,Ft.

### Four roots and fourteen variables

The guard root has degree20 and is uniquely largest; the other roots and
center have degrees17,7,13,and13. Thus the cleared norm's exact degree is
16*20+8*10=400 and its nonzero top part is

    Q0^8 (81 U0^2 S0)^8.

Multiplying by Ff, whose top part is -a0^2*i0^2*c^4, gives degree414.
The top homogeneous form is

    -2^72 3^40 q0^32 a0^34 f^16 Y0^32 k0^32 i0^2 c^4.

In particular

    [j^196 w^66 v^98 h^32 r^2 f^16 c^4] P14
      = -2^402 3^302 beta^196 !=0.

The h^32 selection uniquely takes (h*a0)^32 from k0^32.

### Three roots and fifteen variables

The first Pell root has degree17 and is uniquely largest. The norm has degree
8*17+4*10=176 and nonzero top part

    Q0^4 (9 U0^2 Dt0)^4.

Multiplying by Ff and Fg gives degree176+14+28=218. The top part is

    -2^27 3^9 q0^16 a0^18 f^8 X0^8 Y0^20 k0^12 i0^2 c^4.

Consequently

    [j^104 w^38 v^50 r^2 f^8 h^12 c^4] P15
      = -2^209 3^151 beta^104 !=0.

### Two roots and sixteen variables

Write p=UV+s where

    s=Un+M*b0+H(v-q^2),   deg(s)=7.

The exact identity

    delta*(p^2-A)-Cn
      =delta*(s^2+2UVs-A)-U^2*(V^2-1)

has degree at most30. The other term of N2 has degree60. The top part of
N2 is

    4Q0^2 U0^2 V0^2 (s0^2-A0),
    s0=M0*a0*(4n+c), A0=M0^2*a0^2*c^2,

or equivalently

    2^13 q0^8 a0^8 f^8 R0^2 n(2n+c).

This is nonzero and proves exact degree60 for N2. Multiplication by the three
retained unit factors gives degree60+14+28+22=124. One explicit coefficient is

    [j^58 w^18 v^24 r^2 h^6 f^8 z^2 n^2 c^4] P16
      = 2^113 3^77 beta^58 >0.

The selections h^6,then z^2,then n^2 uniquely isolate the indicated terms
from k0^6,R0^2,n(2n+c). The total exponent is124. Thus no cancellation of
specialized fixed coefficients can invalidate the exact-degree statement.

## Literal validation

The coefficient bytes are authenticated and regenerated from their retained
finite recipe. `verify.py` checks topology, every input's liveness, live
operation counts, actual-coefficient univariate degree attainment and the
displayed top forms. For each form it independently multiplies all conjugate
linear factors in the appropriate free quadratic algebra on72 signed modular
assignments, including v=0,c=0 and their intersection. These are finite
transcription checks; the universal arguments above prove the new equivalences.
The full source/compiler consistency calibration remains the named inherited
ordinary theorem, not a consequence of testing.
