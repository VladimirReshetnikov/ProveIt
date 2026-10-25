# Signed odd radix with a spherical joint factorial/digit certificate

This is the complete ordinary arithmetic proof for the Round 20 semantic
delta from the Shared Factorial Error source. It is a proof relative to
explicitly retained Pell classification, frame construction, source
calibration and cofinal CRT results; it does not claim a newly completed
end-to-end proof-assistant theorem. Finite algebraic transformations of this
source into smaller quartics require their separate literal certificates.

## 1. Literal arithmetic interface

All coordinates are unrestricted integers. Retain the square frame, the
squared semantic anchor, deterministic comparison center, and the complete
both-coordinate orientation pool on all fourteen principal Pell pairs.
Retain all eighteen genuine power requests, every normalized digit row,
the strict amplification index x, and the original beta spacing and endpoints.
Their meanings will be established in order, not assumed initially.

Write t=16+d^2, with integer d. The arithmetic registers are F,B,V,x,y,N,q,M,
and H=1+sum_{nu=1}^9 a_nu, where a_nu are the actual shifted representatives.
The power requests include V at base F^2+1 and index t, N at base B and
index x, q at base BH and index x, M at base q and index x, and the
binomial numerators and denominators. The beta equations are

    y=V(V-1),
    x=F+1+(y+1)u_0,
    x=1+[1+(t+1)y]u_t.

There are eleven low-digit remainders, with denominators q^t (two),
q^(t+1) (five), q^(y+1) (two), and M=q^x (two). The three retained
ratio rows assert L_i v_i=M at the smaller denominator levels. All displayed
powers denote existing polynomial output registers, not variable-exponent
operations in the literal equation. The normalized digit rows have the form

    v_i U_i=M Q_i+R_i,

with the original high quotient Q_i (sometimes an already represented
product). At the largest level v_i=1 without a new coordinate.

Replace the three old front sign guards and the old ceiling rows by

    q=2z+1,
    B v=M,
    MF=vV+S,
    M^2=2(S^2+sum_{i=1}^{11} R_i^2)+G(a,b,c),            (1)

where G(a,b,c)=a^2+b^2+c(c+1). These are literal quadratic rows in their
actual registers. G is nonnegative at every integer triple. Conversely,
every nonnegative integer n is represented: the three-square theorem
represents 4n+1; exactly one of the squares is odd modulo4, so write it as
(2c+1)^2 and the others as (2a)^2,(2b)^2, then divide by4.

## 2. Orientation independent of front signs

The unchanged square frame gives an integer W>=258 such that every
actual base, requested index and proposed output has absolute value <W.
Its main center A satisfies |A|>W^W and |A-1|>4W^3. These assertions use
squares of signed atoms; they do not require any of the removed front signs.
Let a=|A|. The anchor is U^2-(A^2-1)C^2=1 with proposed index h, and

    C^2=h^2+1+sum_nonanchor y_j^2+G_0.

Thus C!=0, |h|<|C| and every other ordinate has magnitude <|C|.
The comparison construction retains

    H_p^2-(A^2-1)J_p^2=1,    J_p=C^2(2e+1),
    f=(1-A)H_p,              D=A+H_p f,
    S_p^2-(D^2-1)R_p^2=1,
    S_p=U+H_p g,             R_p=h+Ck.

The deterministic identity

    D=1-(A-1)(A^2-1)J_p^2

gives |D|>1, D=A modulo H_p and D=1 modulo C, for either sign of A.
Classify |C|=Y_i(a), |J_p|=Y_l(a), with positive indices i,l.
When i>=2, squared-ordinate divisibility gives |C||l and l>i.
For clarity: strong divisibility gives i|l; writing l=ik, Pell expansion
shows Y_l/Y_i=k X_i^(k-1) modulo Y_i. Since gcd(X_i,Y_i)=1,
Y_i^2|Y_l implies Y_i|k and hence |C||l.

The comparison pair has an index j>=0 at signed center D, up to independent
coordinate signs. Polynomial transfer of the abscissa through D=A modulo H_p
and the comparison abscissa residue gives

    X_j(a)=+/-X_i(a) modulo X_l(a).

Abscissa separation implies j=+/-i modulo2l. One elementary proof reduces
indices to [0,l] using X_(n+2l)=-X_n and X_(2l-n)=-X_n modulo X_l.
For r,i<l, X_r+X_i<=2X_(l-1)<X_l, so the reduced congruence forces r=i;
r=l has zero residue and cannot occur. Signs of A,D are absorbed into
the independent coordinate sign. Meanwhile D=1 modulo C and R_p=h modulo C
give j=+/-h modulo |C|. Since |C||l,
i=+/-h modulo |C|. Growth Y_i(a)>=i+2a-2 and |h|<W imply
i+|h|<|C|. Thus i=|h|<W and h!=0. The cap bounds every other index by i.

The exception i=1 has |C|=1, hence h=0 and all other ordinates zero.
All actual indices are then bounded by W independently. Reduce the complete
orientation pool modulo A-1. Classified signed pairs have abscissa residues
s_j in {-1,1} and ordinate residues r_j in {-j,j}, including signed A.
The small error sum

    E=sum_all [(s_j-1)^2+(r_j-k_j)^2]

is nonnegative and less than 4*14*(W^2+1)<4W^3<|A-1|. In the exceptional
case its anchor ordinate contributes1, contradicting the asserted divisibility.
In the nonexceptional case the same bound forces E=0. Therefore both
coordinates of all fourteen principal pairs are the canonical Pell polynomials
(X_k(A),Y_k(A)) at their signed requested indices. No selective-orientation
variant with missing abscissa tests is being assumed here.

## 3. Exact powers at signed and unit bases

Let |n|,|m|,|k|<W and T=2An-n^2-1. For |n|>=2,

    |T|>4W^W-(W-1)^2-1>W^W+W.

Modulo T, (n-A)^2=A^2-1 and n(2A-n)=1. Thus the canonical Pell
expression X_k(A)+(n-A)Y_k(A) is congruent to n^k for k>=0, or to its
modular inverse at negative k. For k>=0 the difference |m-n^k| is below
W+W^W<|T|, so the power row gives m=n^k. For k=-j<0, multiply by n^j:

    mn^j=1 modulo T,
    |mn^j-1|<W^W+1<|T|.

The resulting integer equality mn^j=1 is impossible for |n|>=2, j>=1.
Hence such a request itself forces k>=0 and its exact power meaning.

At n=epsilon in {1,-1}, T=2A epsilon-2. The sequence
f_k=X_k(A)+(epsilon-A)Y_k(A) has f_0=1,f_1=epsilon and satisfies
f_(k+1)=2Af_k-f_(k-1), forwards and backwards. Since 2A=2epsilon modulo T,
it follows that f_k=epsilon^k modulo T for every signed index k.
Now |m-epsilon^k|<=W<|T|, proving m=epsilon^k. This includes negative
indices at -1 and is essential for the initial signed-radix argument.

## 4. Acyclic recovery of nonzero magnitudes

The oddness row gives q!=0. Apply the preceding lemma immediately to
M's request at base q: if |q|>=2 it gives x>=0 and M=q^x; if q=+/-1 it
gives M=q^x for any signed x. In either case M!=0. This is the correct
source of nonzeroness: unlike the earlier guard with constant1, the
spherical budget alone would not exclude M=0.

The positive t request gives V=(F^2+1)^t>=1 for every signed F. By Bv=M,
B,v are nonzero. Set b=|B| and s=BF-V. The other row gives S=v*s.
Since |S|<=|M|/sqrt(2),

    |s|<=b/sqrt(2)<3b/4.                               (2)

If F=0, then V=1 and s=-1, so b>=2. If f=|F|>=1, opposite signs of
B,F would force V=BF-s<-b+3b/4<0. Thus BF=bf>0. Moreover
V<b(f+3/4). For integer f>=1,

    (f^2+1)^t >= (f^2+1)^2 > (f+1)(f+3/4).

The last difference is f^4+f^2-7f/4+1/4>0. Therefore b>=f+2>=3, and

    V<b(f+3/4)<=b(b-5/4)<b^2-b<b^2.                   (3)

In every branch b>=2. If q=+/-1 then |M|=1, contradicting Bv=M.
Thus Q=|q|>=3, and |q+1|>=2. The nine representative requests at base
q+1 now force every actual a_nu>=0. Hence H>=1. The derived-label
request similarly gives h>=0, and the anchor already excluded h=0.
The request at base q gives x>=0 and M=q^x. The t+1 denominator and
its ratio equation, after taking absolute values, imply x>=t+1>=17.
The self-radix request at base BH, whose magnitude is at least b>=2,
now gives

    q=(BH)^x,    Q=(bH)^x>=b^x>=b^(t+1).              (4)

If F=0, recall that so far only b>=2 was proved. Since q is odd,
(4) makes b odd, hence b>=3. This parity step repairs the zero branch
when changing the old radius1/2 to the new spherical radius.

## 5. The factorial digit at a possibly negative radix

Each normalized row L_i v_i=M has nonzero signed values. Both terms
v_i U_i and M Q_i are divisible by v_i, so v_i|R_i. Therefore
r_i=R_i/v_i is an integer, and division restores U_i=L_i Q_i+r_i.
The spherical budget yields

    |r_i|<=|L_i|/sqrt(2)<3|L_i|/4.                    (5)

This argument does not require either denominator or remainder positive.

For the factorial numerator, n=F^2+t>=t and its exact request gives
U=(q+1)^n. The restored digit row is

    U=q^t(B+q eta)+r.

Write C_j=binom(n,j) and rho=sum_(j=0)^(t-1) C_j q^j, an ordinary signed
polynomial in the possibly negative q. For F!=0, the elementary coefficient
lemma gives C_j<=(F^2+1)^t=V for all j<=t. To prove the lemma in its full
range, induct on t in binom(m+t,j)<=(m+1)^t for m>=1,j<=t. Pascal gives
the next row for j<=t because2<=m+1; the new edge j=t+1 is the product
product_(i=1)^(t+1)(1+m/i)<=(m+1)^(t+1).

Using (3)--(4),

    |rho|<Q^t*V/(Q-1)<Q^t*(2/b^(t-1))<Q^t/32.

For F=0 one must not use V=1 as a coefficient bound. Instead C_j=binom(t,j)
<=2^t. We have b>=3, so

    |rho|<Q^t*2^t/(Q-1)
          <=Q^t*2^t/(3^(t+1)-1)
          <Q^t*(2/3)^(t+1)<Q^t/32.

In both cases r-rho is divisible by q^t, while by (5)
|r-rho|<3Q^t/4+Q^t/32=25Q^t/32<Q^t. Hence r=rho.
Subtract, divide by q^t, and reduce modulo q to obtain
B=C_t modulo q. If F!=0, |B-C_t|<=b+C_t<b+b^2<Q, using (3)--(4).
If F=0, C_t=1 and |B-1|<=b+1<Q. Thus in both cases

    B=binom(F^2+t,t)>0.

F=0 would force B=1 contrary to b>=3. Thus F!=0, and the earlier
common-sign argument gives F>0. Finally q=(BH)^x>0. The negative-radix
possibility has been excluded by the extracted arithmetic, not by assumption.
All other requests, including N=B^x, have their usual positive meanings.

## 6. Nearest factorial at radius3/4

For t>=16, positive integer F and K=t!, put

    R_t(F)=(F^2+1)^t/binom(F^2+t,t)
          =K product_(i=1)^t (F^2+1)/(F^2+i).

We prove |F-R_t(F)|<3/4 if and only if F=K. Each factor is nondecreasing
in F, so R_t(F)>=R_t(1)=2^t/(t+1)>2t^2+3/4. The final inequality holds
at16 and propagates by induction: for A_t=(t+1)(2t^2+3/4),
2A_t-A_(t+1)=2t^3-4t^2-37t/4-4>0 for t>=16.
The distance assumption gives F>2t^2, so F>=2t^2+1. As R_t(F)<K,
integer F satisfies F<=K. Also F^2/(F+1)=F-1+1/(F+1)>2t(t-1), hence
F^2>2t(t-1)(F+1). For u_i=(i-1)/(F^2+i),

    sum u_i<t(t-1)/(2F^2)<1/[4(F+1)].

The product inequality product(1-u_i)>=1-sum u_i gives
R_t(F)>K*(1-1/[4(F+1)]). If K>=F+1 this exceeds F+3/4,
contradicting the distance assumption. Thus F=K.
Conversely at F=K the same product inequality gives

    0<K-R_t(K)<t(t-1)/(2K)<1/32.

The last inequality holds at16 and decreases thereafter. This proves both
directions, including the stronger canonical error bound.

By B=binom(F^2+t,t), inequality (2) is exactly
|F-R_t(F)|<3/4. Thus F=t!, and 0<s=BF-V<B/32. Therefore the original
ceiling witnesses s and B-s-1 are nonnegative integers. Equation (4) now
gives q>B, so the removed output slack q-B-1 is also nonnegative. Fresh
G witnesses restore all three original front sign guards.

## 7. Remaining digits and the retained calibration

Only now use the true positive factorial front in the beta endpoints.
Since y=V(V-1)>F+2 and x>=t+1>0, u_0<=-1 would imply
x<=F-y<0. Hence u_0>=0 and x>=F+1>=2. The last endpoint then forces
u_t>=1, giving x>=2+(t+1)y. Thus all four digit denominator levels are
positive divisors of M. The retained strict amplification estimate is
unchanged: with R=2+t+x+y+F, one has R<2x and x>=16!+1>2^32, so
R^(2^23)<(2x)^(2^23)<2^x. This is the existing local precision margin.

After factorial recovery, B divides C_0+F^2+1. Since B>F^2+1 and
C_0>=0, the encoded index C_0 is nonzero, so H>=2. Each ordinary
representative a>=0 satisfies binom(a,j)<=max(1,a)^k<=H^x at its range
position k<=x, including a=j=0. The retained constructor degree ledger
gives h<=H^(2^22), and the factorial/endpoint inequalities give
2^22(t+1)<x, so all needed derived-label coefficients also are <=H^x.
Since q=B^x H^x, every genuine remaining low tail satisfies

    0<=rho_i<L_i*H^x/(q-1)<L_i*(2/B^x)<L_i/32.

Equation (5) and the same divisible-difference argument force r_i=rho_i.
Every old interval slack L_i-r_i-1 is nonnegative, and its original
product guard has fresh G witnesses. The quotient congruences are exactly
the retained N-divisibility range tests, with N=B^x|q. The existing
prime-power extraction and constructor/Horn-flow theorem yield a finite
C222 refutation. Their named ordinary calibration interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
This recovers an actual calibrated source witness, not merely some of its
necessary arithmetic properties. Stored representative-minus-one coordinates
may still equal -1; only actual semantic representatives need be nonnegative.

## 8. Constructive completeness

Start with a finite calibrated refutation. Use the retained cofinal horizon
t=16+d^2, put F=t!, V=(F^2+1)^t and y=V(V-1), and choose a sufficiently
large beta CRT code x. Its true beta quotients are nonnegative and <x, as
their denominators are at least2. The original strict range tests apply.
Every factor1+F^2/i is odd, since F is even and i|F. Hence B and N=B^x
and the precision modulus N^2 are odd. Adding N^2 to a representative
preserves its CRT residues and reverses parity.

Choose the dominant representative a in [2N^2,4N^2) with parity opposite
b; retain the other representatives in (0,2N^2]. The literal constructors
give h>=2a^2 and h=1+a+b modulo2. Thus h is even and remains a dominant
semantic anchor. Choose a third independent representative's parity so the
sum of all nine is even, making H odd. These are independent choices
because N^2 is odd. Consequently q=(BH)^x is odd, and z=(q-1)/2 is an
integer. No parity constraint on x is necessary for affine oddness.

For the deterministic center choose an admissible positive A and C=Y_h(A),
U=X_h(A). Since h is even, C is even and U odd. Set l=hC. Composition gives
J_p=Y_l(A)=C Y_C(U). The Pell binomial expansion and
U^2-1=(A^2-1)C^2 imply Y_C(U)/C=U^(C-1) modulo C. In detail each term
of degree2j in U^2-1 is divisible by C after division by C for j>=1,
whereas the j=0 term is U^(C-1). Hence J_p/C^2 is an odd integer, supplying e.
Set H_p=X_l(A), f=(1-A)H_p, D=A+H_p f. The comparison pair
(X_h(D),Y_h(D)) supplies the required abscissa residue modulo H_p and
ordinate residue modulo C, even when D<0. The retained frame and cap
construction supplies its remaining witnesses. All canonical pair errors
are divisible by A-1, so the full orientation pool also holds.

Since B|q and x>0, B|M=q^x. Set v=M/B and S=v(BF-V). The nearest
factorial estimate gives 0<S<M/32. For each genuine digit remainder,
set R_i=(M/L_i)r_i. The retained bounds give 0<=R_i<M/32. Therefore

    2(S^2+sum R_i^2)<24M^2/1024=3M^2/128<M^2.

The integer difference is nonnegative and has a G representation, proving
(1). All other source witnesses are retained. This constructs a new zero
from every finite refutation; it is not a pointwise claim about arbitrary
old private witness assignments or uniqueness of the ternary guard.

## 9. Conclusion and exact scope

Sections2--7 give soundness and Section8 gives completeness. Thus relative
to the identified retained ordinary calibrations, ZFC proves that the new
literal source has an integer zero if and only if a finite ZFC refutation
exists. Every separately certified integral coordinate shear, elementary
residual operation, and monic projection preserves this existence theorem.
The sum of squares of a final quadratic residual list is zero exactly when
all rows vanish. Negating the resulting equivalence gives integer
unsolvability equivalent in ZFC to Con(ZFC). No proof of consistency, global
minimality, or new formal-kernel endpoint is claimed.
