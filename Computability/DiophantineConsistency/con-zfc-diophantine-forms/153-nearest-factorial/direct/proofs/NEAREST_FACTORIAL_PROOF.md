# Nearest factorial certificates and a shared signed residue budget

Prepared with AI assistance, 25 October 2026. This is the new mathematical delta
for `common_nearest246`; the later affine/row reductions are exact polynomial
identities. It uses the complete signed C222 arithmetic source of the common
252-variable incoming equation. Its logical calibration is inherited, not a
newly kernel-checked theorem.

## 1. Exact change

Retain the signed Pell frame, semantic anchor, both-coordinate orientation,
all eighteen power requests, the strict exponent K=x, and the eleven normalized
low-binomial-digit equations from the common-remainder construction. In their
semantic notation, t>=16,

    V=(F^2+1)^t,    y=V(V-1),
    N=B^x,         q=(BH)^x,        H=1+sum nine representatives,
    M=q^x.

The four existing low-digit denominators are q^t, q^(t+1), q^(y+1), and M.
Their three existing ratio equations say L_i v_i=M. Each low digit is represented
by R_i=v_i r_i, with a literal scaled numerator equation. These expressions
name existing ordinary polynomial coordinates; no variable power is part of
the delivered quartic.

Delete all three front nonnegativity guards, on the original factorial
remainder, its slack, and the radix output slack. Delete the two original
ceiling equations, whose joint meaning was

    BF=V+s,          B=r+s+1.

Introduce two integer coordinates v_B,S and replace them by

    B v_B=M,         v_B V+S=M F.                         (C)

Require an odd square radix q=(2z+1)^2, with one new integer coordinate z.
Use the single common budget

    M^2=1+4*(S^2+sum_(i=1)^11 R_i^2)+a^2+b^2+c(c+1).    (B)

All old and new coordinates are unrestricted integers. The shared squared Pell
anchor keeps its own independent ternary nonnegative guard. The old raw radix
output relation q=B+o+1 remains, but its sign guard is removed.

In the actual quadratic source (C) is two residuals of degree two. Both old
ceiling coordinates occur only in the two deleted ceiling rows; their exact
absence elsewhere is checked. The original product coordinate BF becomes
unused and is eliminated by the ordinary monic projector. The new coordinates
v_B,S do not enter the retained Pell frame or power requests.

## 2. Signed-base power lemma

The retained frame and signed-anchor proof canonically orient both Pell
coordinates X_k(A),Y_k(A) for each possibly signed requested index k, before
any of the deleted front guards is used. Its square frame bounds every original
base n, output m, and requested index by W in absolute value, and |A|>W^W.
For T=2An-n^2-1, the usual Pell polynomial identity gives

    X_k(A)+(n-A)Y_k(A) = n^k modulo T                  (k>=0).

For n!=0, T=-1 modulo n, so n is invertible modulo T. The multiplication law
extends this congruence to negative k in the modular sense. Thus if |n|>=2
and k=-j<0, the literal output row gives m*n^j=1 modulo T. But

    |m*n^j-1|<W^W+1<|T|,

so m*n^j=1 in the integers, impossible. Therefore k>=0 and the same size
bound gives m=n^k exactly. This proof permits n<=-2 as well as n>=2.
For n=1, every signed k gives m=1 exactly: the modular power is 1 and
|m-1|<|T|. For n=-1 the analogous exact output is (-1)^k; that case is
not needed after the bootstrap below.

This extends the inherited positive-base lemma only by using absolute values
and the same modular inverse; it adds no new hypothesis about the sign of n.

## 3. The radix is at least two

The odd-square row gives q>=1. The V request has positive exponent t and
base F^2+1>=1, so the signed-base lemma (including n=1) gives
V=(F^2+1)^t without assuming a sign for F or B.

If q=1, its requested exponent x may be signed, but the n=1 case gives
M=1. Budget (B) forces S=0. The first equation (C) gives B v_B=1, hence
B=v_B=1 or B=v_B=-1. The second then gives F=v_B V, impossible because
V=(F^2+1)^t>|F|. Hence q>=2.

The q^x request now forces x>=0 and M=q^x>0. The q^(t+1) request and its
ratio equation give q^(t+1) v=M. Since v is an integer and q>=2, necessarily
x>=t+1>=17. This elementary divisibility consequence replaces the earlier
bootstrap from the signed beta endpoints.

Every representative is an exponent in a request with base q+1>=3. Thus all
nine actual representatives are nonnegative and H>=1. This deduction does
not use the low-digit remainder bounds. The derived-label exponent is also
nonnegative, and the retained nonzero anchor makes it positive when needed.

## 4. A signed nearest-ceiling relation

Equation B v_B=M gives B!=0 and v_B!=0. Put b=|B| and define the integer

    s=BF-V.

Equations (C) imply S=v_B s. Budget (B) gives |S|<M/2 and therefore

    |s|<b/2.                                            (1)

At this stage s is allowed to be negative. This is not the old ceiling
hypothesis and must not be used as one.

### Excluding F=0

If F=0, then V=1 and s=-1, so (1) implies b>=3. Since H>=1, the signed-base
lemma applies to BH and yields q=(BH)^x. Since q>0,
q=(bH)^x>=b^x>=3^(t+1). Here x>=t+1 was already established.

The factorial numerator is (q+1)^t. Its coefficients through degree t are
bounded by 2^t. Its ordinary low part below position t satisfies

    0<=rho<q^t * 2^t/(q-1)
          <=q^t*(2/3)^(t+1)<q^t/32,                    (2)

using t>=16. The normalized factorial remainder has absolute value below
q^t/2 by (B), and its scaled digit row makes it congruent to rho modulo q^t.
As in the common-remainder lemma, division by the exact ratio is integral.
Modular uniqueness thus identifies it with rho. The exact digit equation
then implies B=binom(t,t)=1 modulo q.

But |B|=b<q-1, so the only integer in this range congruent to 1 modulo q is
B=1, contradicting b>=3. Therefore F!=0.

### Excluding negative F and B

Let f=|F|>=1. If BF<0, then BF<=-b and V=BF-s<-b/2<0, impossible.
Thus BF=bf>0. From (1),

    V< b*(f+1/2).                                       (3)

For f>=1 and t>=2 one has

    V=(f^2+1)^t >=(f^2+1)^2 >(f+1)*(f+1/2).

Consequently b>=f+2. Equation (3) now gives

    V<b^2-b.                                            (4)

In particular |BH|>=3. The signed-base lemma again gives
q=(BH)^x=(bH)^x>=b^x, with x>=17. Every binomial coefficient
binom(F^2+t,j), 0<=j<=t, is at most V=(F^2+1)^t. The elementary coefficient
lemma is stated below. Therefore its ordinary low remainder satisfies

    0<=rho<q^t*V/(q-1)<q^t*(2/b^15)<q^t/32.             (5)

The normalized budget again identifies the factorial remainder exactly.
Writing C=binom(F^2+t,t), the digit equation gives C=B modulo q, with
1<=C<=V<q. If B<0, then b<q and necessarily C=q-b. But by (4),

    C=q-b>=b^2-b>V,

a contradiction. Thus B>0 and F>0, and now C=B exactly.

No factorial fixed-point identity has been assumed in Sections 2-4.

## 5. A nearest-integer factorial fixed-point theorem

Let t>=16 and F be a positive integer, put K=t! and

    R_t(F)=(F^2+1)^t/binom(F^2+t,t)
          =K * product_(i=1)^t (F^2+1)/(F^2+i).

Then

    |F-R_t(F)|<1/2    if and only if    F=K.             (6)

Each factor is nondecreasing in F, so R_t(F)>=R_t(1)=2^t/(t+1).
For t>=16, 2^t/(t+1)>t^2+1/2 (verify at 16; the cubic right side grows by
less than a factor two at each succeeding integer). Thus |F-R_t(F)|<1/2
implies F>t^2, and hence F>=t^2+1. Also R_t(F)<K, so the same hypothesis
implies F<=K.

Put u_i=(i-1)/(F^2+i). Since F>=t^2+1,

    F^2>t*(t-1)*(F+1),
    sum u_i<t*(t-1)/(2F^2)<1/(2(F+1)).

The elementary product inequality product(1-u_i)>=1-sum u_i therefore gives

    R_t(F)>K*(1-1/(2(F+1))).

If K>=F+1, this is at least F+1/2, contradicting the assumed distance.
Thus K=F. This proves the difficult direction without a three-range split.

For every positive F, the same product estimate gives

    0<K-R_t(F)<K*t*(t-1)/(2*(F^2+1)).                   (7)

At F=K it follows that

    0<K-R_t(K)<t*(t-1)/(2K)<1/32,                       (8)

where the last inequality is immediate at 16 and preserved by induction.
Thus F=K satisfies (6), with a stronger canonical completeness margin.

By Section 4, B=C and s=BF-V. Relation (1) becomes
|F-R_t(F)|<1/2. Hence F=t!. Equation (8) also shows s>0 and s/B<1/32.
In particular s<B and the old ceiling coordinates can be restored as
r=B-s-1>=0 and s>=0. The old output slack o=q-B-1 is nonnegative since
q>=B^x>=B^2>B. All deleted front guards therefore have fresh ternary witnesses.

## 6. The elementary coefficient bound used above

For m>=1,t>=1, and 0<=j<=t,

    binom(m+t,j)<=(m+1)^t.

Induct on t. At t=1 it is immediate. For j<=t, Pascal's identity bounds
both terms by (m+1)^t and hence their sum by (m+1)^(t+1). The new edge
j=t+1 has product formula product_(i=1)^(t+1)(1+m/i)<=(m+1)^(t+1).
Taking m=F^2 proves the bound used in (5). When F=0 use binom(t,j)<=2^t
instead; applying the m>=1 statement blindly to m=0 would be unjustified.

## 7. Recovering the remaining digits and the inherited arithmetic

After F=t!, all old front signs and the old ceiling have been restored.
The retained endpoint equations now imply x>=2+(t+1)y just as in the parent.
The existing strict-budget bound, derived-label bound, self-sized radix, and
ordinary representative estimates therefore apply. Each of the ten range
low residues is below its original denominator divided by 32. The common
normalized budget identifies them by modular uniqueness. Every old interval
slack and product guard has a fresh nonnegative/ternary witness, and the
original N-divisibility range conditions are restored.

The inherited arithmetic source now yields a finite C222 refutation, and its
named ordinary logical calibration yields a finite ZFC refutation. This is
soundness, without any assumption that ZFC is consistent.

## 8. Constructive completeness

Start with a finite C222 refutation. Use the inherited cofinal t>=16,
F=t!, beta CRT, amplified CRT, semantic-anchor parity, and private Pell witness
construction. Choose the beta code x positive and even: its moduli are odd,
so adding their odd product changes parity while preserving all congruences.
Choose the independent CRT representative parities so a,b have opposite parity
(as the even semantic anchor requires), while their total is even and H odd.
The independent odd modulus N^2 permits both choices and the same dominant
representative lift as in the parent. These parity choices are exactly those
of the credited odd-square-radix construction.

B is odd, H is odd, x is even, and q=(BH)^x is an odd square. Set
z=((BH)^(x/2)-1)/2. Since B divides M=q^x, set v_B=M/B. With s=BF-V>0,
set S=v_B s. By (8), 0<S<M/32.

For each old low-digit residue r_i, set R_i=(M/L_i)r_i. The unchanged genuine
binomial estimates give 0<=R_i<M/32. All twelve normalized entries, including
S, therefore satisfy

    4*(S^2+sum R_i^2)<48*M^2/1024=3*M^2/64<M^2.

The integer M^2-1-4*(S^2+sum R_i^2) is nonnegative. The universal ternary form
a^2+b^2+c(c+1) represents it, so (B) has integer witnesses. Equations (C) are
literal identities. Every remaining inherited witness is retained. This
constructs a zero of the new source from every finite refutation.

## 9. Exact polynomial and proof scope

The base source is emitted as a literal quadratic residual system over all
integers. Its single polynomial is the sum of residual squares. Horn factoring,
integral monic projection, coordinate translations, and the later affine-row
reductions have explicit exact restoration certificates. They preserve integer
existence; row shears preserve the common zero set but need not preserve the
sum-of-squares polynomial itself.

The 246-coordinate stage has 182 quadratic residuals. Four affine consequences
remove four further coordinates, giving a 242-coordinate endpoint; a three-
projection version keeps a denser semantic-label coordinate and gives 243.
The completed final metrics are in the generated METRICS.json files.

Combining Sections 2-8 with the retained C222/ZF/ZFC refutation calibration
proves in ZFC that a zero of each fixed delivered polynomial exists exactly
when there is a finite syntactic ZFC refutation. Negation is the required
unsolvability equivalence with Con(ZFC). This proves neither side separately.
Finite artifact checks certify the emitted polynomials and transformations;
they do not substitute for the unbounded ordinary proof above or its named
inherited calibration.
