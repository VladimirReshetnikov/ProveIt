# Combining the squared-modulus quotient with ordinary strong rank

## Result, comparison, and limits

This packet adds nine local fifteen-positive-variable degree/operation tradeoffs:
(operations, exact degree) = (67,125), (68,101), (69,91), (70,84),
(71,80), (72,74), (73,60), (74,50), (75,46).
It also lowers the fourteen-positive-variable 79-operation degree from 56 to 52.
All are single ordinary integer-coefficient polynomial equations. Their lack
of positive solutions is provably equivalent in ZFC to Con(ZFC), at the
ordinary mathematical proof level of the inherited calibrated compiler.
No end-to-end new Lean/Rocq certificate or formal object-language derivation
is claimed, and no claim that ZFC is consistent is made.

The new contribution is a synthesis and regrouping of existing ingredients,
not invention of the squared-modulus trick, ordinary strong-rank theorem,
Pell-root gaps, or quotient absorber. Incoming package 51 already gives
66 operations / degree 157 and the squared-modulus lemma. Incoming package
49 gives 76 / 44; incoming package 50 gives 14 variables at 79 / 56.
Wave 7 gives 72 / 80. Earlier historical points include 67 / 155,
68 / 123, 69 / 99, 70 / 93, 71 / 83, 74 / 56, and 78 / 44.
The incoming normalized squared-modulus points 68 / 113 and 72 / 80
are also comparators. None is silently discarded.

In particular the absolute operation record remains the inherited 66 / 157;
the degree-44 point remains the inherited 76 / 44. The rebuilt 76 / 44
reference is included solely as a control. The new points are bounded
repository comparisons at authenticated pins, not global optimality claims.

## 1. Explicit coherent coefficient tuple

All circuits bind every port together to the materialized Wang943
121-by-8801 compiler tuple: B=2^1064921, beta=B-1, K0=K, MC=MC,
MF=MF_source=MF_native+B-1. Each gzip payload is an unsigned
little-endian integer; its raw/compressed hashes and byte lengths occur
in COEFFICIENT_BINDING.json. The complete coefficient interface and proof
are in upstream/COEFFICIENT_PROOF.md. The authoritative local binding
points there, not to the inert relative paths in historical source files.
The archive provenance, source text hashes and placement pin are in
SOURCE_PINS.json. No ports from different tuples are mixed.

For the 15-variable equations the supplied positive coordinates are
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma. A first gap replaces tau by r;
an auxiliary gap replaces y by u, without changing the coordinate count.
All subsequent letters are polynomial abbreviations, not hidden witnesses:

 q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
 k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
 Delta=a^2+H=(a+2)^2-1, D=X+ac+gamma H,
 L=E kY,
 R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
 V=f^2(cT-R)-c, Aaux=Delta(f^2-1), I=ic^2.

The ordinary norm factors are

 N0=tau^2-L(L+k),              N1=D^2-Delta c^2,
 Na=Aaux(V^2-y^2)+y^2,         Nk=k-hE-R,
 Nt=(K0+w)C+(q-F)-z(q-1),      S=I^2-Aaux, Ns=S+1.

Use the alternatives

 N0_gap=r^2+L(2r-k),
 Na_gap=(V+u)^2-Aaux*u*(2V+u)

where the indicated root gap is enabled. Define Q(B1,...,Bm) to mean
S^2 + sum_j (product of the factors in Bj - 1)^2. This is only compact
notation for a fixed polynomial, and every product/addition is charged.

The literal evaluators implement:

- 68 / 101: N0 N1 Na Nk Nt Ns - 1, no gaps.
- 69 / 91: the same product, first gap only.
- 70 / 84: the same product, both gaps.
- 71 / 80: Q({N0,N1},{Na,Nk,Nt}), no gaps.
- 72 / 74: Q({N0,N1,Nk},{Na,Nt}), first gap only.
- 73 / 60: Q({N0},{Na},{N1,Nk,Nt}), no gaps.
- 74 / 50: Q({Na},{N1,Nk},{N0,Nt}), auxiliary gap only.
- 75 / 46: Q({Na},{N0,Nk},{N1,Nt}), both gaps.

For 67 / 125 only, set I_sc=i*Delta*c^2 and
Nsc=Delta*f^2-I_sc^2. The equation is

 N0 N1 Na Nk Nt Nsc - Delta = 0,

with no gaps and the same reduced Aaux in Na. Its evaluator shares
Delta*f^2 between Nsc and Aaux=Delta*f^2-Delta. This is the squared-modulus
version of the inherited reduced scaled product, not a new strong-rank lemma.

## 2. Universal squared-modulus reconstruction

Write chi_A(n), psi_A(n) for the integer Pell polynomials, with
chi_A(n)^2-(A^2-1)psi_A(n)^2=1. The inherited canonical compiler witness
has A=a+2, c=psi_A(R), R=3 modulo 4 and, for the ordinary strong coordinate,

 I^2=Delta(f^2-1), I>1, c divides I, f^2=1 modulo c.

These follow either from the inherited ordinary rank theorem or from a
normalized witness by i_ordinary=Delta*i_normalized. The congruences
below require exactly these hypotheses, not the unjustified assertion
that an arbitrary ordinary i is divisible by Delta.

For R=2r0+1 there is an integer polynomial Q_r0(Z) satisfying
chi_t(R)=t Q_r0(t^2), Q_r0(0)=(-1)^r0 R, and
Q_r0(1-A^2)=(-1)^r0 psi_A(R).
These are polynomial identities. For example Q_0=1, Q_1=4Z-3 and
Q_(j+1)=(4Z-2)Q_j-Q_(j-1); substitution gives the second identity
by the corresponding odd-index Pell recurrence. Since r0 is odd, put

 V*=chi_I(R)/I, y*=psi_I(R).

Then V* and y* are positive integers, and

 Aaux((V*)^2-(y*)^2)+(y*)^2=1,
 V*=-c modulo f^2, V*=-R modulo c.

Indeed I^2=1-A^2 modulo f^2, and I^2=0 modulo c. Also gcd(c,f)=1.
Therefore V*+c+Rf^2 is divisible by cf^2, and

 T*=(V*+c+Rf^2)/(cf^2)>0,
 V*=f^2(cT*-R)-c.

This works for ordinary as well as normalized strong witnesses.
It does not say that every older T is divisible by f. Instead it replaces
the auxiliary ordinate and quotient by canonical positive ones.
For soundness the exact all-value polynomial identity is much simpler:

 c((fT)f-1)-Rf^2 = f^2(cT-R)-c.

Thus every new assignment pulls back to the old quotient at T_old=fT.

## 3. Gap pullbacks and positivity

The exact identities are

 (L+r)^2-L(L+k)=r^2+L(2r-k),
 Aaux(V^2-(V+u)^2)+(V+u)^2
   =(V+u)^2-Aaux*u*(2V+u).

At a new zero, restore tau=L+r>0 and y=|V+u| whenever these gaps
are present. The auxiliary root cannot vanish once Aaux=I^2>1 and
Na is a unit: otherwise Na=I^2 V^2 is not +1 or -1.
Hence y>0. No unsupported sign assumption on V+u is needed.

For completeness take a canonical compiler witness, first perform the
squared-modulus reconstruction, and then put r=tau-L and u=y*-V*.
The first norm gives tau^2-L^2=Lk+1>0, hence r>0. Since I>1 and
R>=3, the explicit Pell quotient V*=chi_I(R)/I exceeds 1. The auxiliary
norm gives (I^2-1)((y*)^2-(V*)^2)=(V*)^2-1>0, so y*>V* and u>0.
Thus every enabled coordinate substitution preserves existence in both
directions, with all supplied unknowns strictly positive.

## 4. Unit signs and inherited soundness

For the ordinary product, every factor is an integer unit. The
check needed to use its strong unit is the following complete mod-four
check: Delta is 0 or 3 modulo 4, and I^2,f^2 are 0 or 1 modulo 4, so

 1+I^2-Delta(f^2-1) is never -1 modulo 4.

Therefore Ns=1 and S=0. For the sum-of-squares equations S=0 is immediate.
In both cases Aaux=I^2 is a square. The consecutive-product negative Pell
obstruction excludes N0=-1, including after the first-gap pullback.
For clarity, if x^2-n(n+1)t^2=-1 with n>=2 and least positive t, then
nt<|x|<(n+1/2)t and t'=(2n+1)t-2|x| is an integer strictly between
0 and t. Multiplying by the inverse norm-one unit gives another solution,
a contradiction. Here n=XY^2>=2.

Also N1 cannot be -1 modulo 4 because Delta is 0 or 3. Finally
Na=I^2 V^2-(I^2-1)y^2 is congruent to either y^2 or V^2 modulo 4,
so Na cannot be -1. Consequently

 N0=N1=Na=1, Nk and Nt are units, Nk*Nt=1, S=0.

This conclusion holds for every listed grouping: multiplying its grouped
unit equalities accounts for all five factors exactly once. The pulled-back
assignment therefore zeros the inherited relaxed P72 equation. Its full
soundness proof is reproduced in upstream/RELAXED_PROOF.md: weak transport
retains the possible C=0 boundary, large-index growth precedes the ordinary
rank theorem, the signed auxiliary step-down recovers p=R, and only then
the remaining signs become Nk=Nt=1 and C>0. Its coefficient/compiler and
blank-K215/refutation calibration then give a finite ZFC refutation.
We do not skip that sign-recovery step or silently assume C>0 early.

For the scaled 67 / 125 equation, Nsc=Delta*(f^2-Delta*i^2*c^4).
Cancel the nonzero positive Delta in the final equation. The resulting
normalized strong factor is a unit and cannot be -1 modulo 4. It equals 1,
so Nsc=Delta and Aaux=I_sc^2. The same norm signs and inherited normalized
proof apply. This is exactly the established reduced scaled product
interface plus T_old=fT; its proof is included in the squared-modulus
source and inherited Pell audit. Completeness uses the normalized canonical
witness and Section 2 with I_sc in place of I.

Conversely, a finite ZFC refutation gives the authenticated canonical
compiler witness. Section 2 replaces only T,y; Section 3 supplies each
enabled positive gap. All individual factors then equal 1, S=0, and
Nsc=Delta in the scaled case, so every displayed polynomial vanishes.
This proves the promised equivalence after negating existential solvability.

## 5. Fourteen positive variables, degree 52, 79 operations

Remove h, retain tau, and replace y by u. Keep the common abbreviations,
ordinary I=ic^2, squared-modulus V and auxiliary gap Na_gap. Set

 U=4q^4, r0=k-R-1, b0=X+ac,
 Dstar=U b0+H(U gamma-r0), Gmain=1+Delta c^2.

The single equation is

 (Dstar^2-U^2 Gmain)^2 + (I^2-Aaux)^2
   + (Na_gap-1)^2 + (N0 Nt-1)^2 = 0.

The fully charged evaluator has 79 operations. This is the incoming
fourteen-variable 79 / 56 absorber with one gate saved by the squared
quotient and one gate added by the auxiliary root gap. Soundness is a
direct pullback to that exact old polynomial: T_old=fT, y=|V+u|.
Here the strong residual gives Aaux=I^2>1 and Na_gap=1 excludes y=0.
The old absorber proof, included as upstream/FOURTEEN_PROOF.md, establishes
its early large-index bound before invoking ordinary strong rank and
reconstructs the deleted positive h and the original positive gamma.
No new quotient-absorption or rank claim is substituted for that proof.

For completeness start with a canonical normalized compiler witness,
convert its i to ordinary form, apply the absorber's positive gamma shift,
and then use Sections 2 and 3 to obtain T and u. The absorber coordinates
other than the auxiliary pair are untouched. This yields a positive root.

The main residual already has degree 26, so this method yields degree 52,
not degree 44. Its exact expansion identity is

 Dstar^2-U^2 Gmain
 = U^2((b0+H gamma)^2-Gmain)
   -2UH r0(b0+H gamma)+H^2 r0^2.

The three terms have degrees 26, at most 25, and at most 20. The other
three residual degrees are 22,23,24. This also identifies the limitation
of simply combining the known absorber and root gaps.

## 6. Exact degree and finite evidence

Put Q=beta J, k0=eta+zeta and C1=Q-F-alpha. The exact factor degrees
with the squared-modulus quotient are:

 N0:22 or 12 with first gap; N1:18; Na:30 or 23 with auxiliary gap;
 Nk:7; Nt:2; S:22; Ns:22; Nsc:46.

The main cancellation is the all-value identity, Z=X+gamma H,

 (ac+Z)^2-(a^2+H)c^2 = Z^2+2acZ-Hc^2.

The useful leading forms are

 N0_top=-w^2 s^4 k0^2 Q^14,
 N0gap_top=w s^2 k0 Q^7(2r-k0),
 N1_top=8 gamma w^2 s^3 k0 Q^11,
 Na_top=w^2 s^4 k0^2 Q^14 T^2 f^6,
 Nagap_top=-2w^2 s^3 k0 Q^11 T f^4 u,
 Nk_top=-hwsQ^4, Nt_top=w C1-zQ,
 S_top=Ns_top=i^2 k0^4 s^4 Q^12,
 Nsc_top=-i^2 w^4 s^8 k0^4 Q^28.

Their products give the claimed degrees. For squared sums, a nonzero
leading square cannot cancel over the real polynomial ring. In particular
75 / 46 has leader 4w^4 s^6 k0^2 Q^22 T^2 f^8 u^2, and 74 / 50 has
leader 64 gamma^2 h^2 w^6 s^8 k0^2 Q^30. The 14-variable leader is
16384 gamma^2 w^4 s^6 k0^2 Q^38, of degree 52.

The independent auditor expands each actual main-norm ancestor cone
exactly, then propagates nonzero symbolic homogeneous forms. For every
output it exhibits a nonzero monomial whose coefficient depends only on
the authentic nonzero beta, so symbolic coefficient-port cancellations
cannot disappear after the fixed tuple is bound. All binary operations,
including constant multiplications, are charged, and every producer,
witness and coefficient port is checked live. It also checks all
coefficient payload hashes/ranges/populations and the inherited proof-text
hashes. There are 100 signed/degenerate full-formula diagnostics per circuit
and five exact canonical Pell reconstruction examples.

Run python3 build.py, python3 audit.py, and python3 -O audit.py. The latter
two produce identical audit results. These finite checks certify the
literal arithmetic artifacts, not Con(ZFC) or the unbounded compiler proof.
