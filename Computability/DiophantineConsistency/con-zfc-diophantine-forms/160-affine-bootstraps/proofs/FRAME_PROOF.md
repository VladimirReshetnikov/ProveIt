# Affine bounds, a positive horizon, and difference errors

This note proves the final `horizon8_difference_frame` source delta. It is
an ordinary mathematical argument composed with the independently proved
linear-selector, signed-radix, affine-beta, and C222 calibration arguments.
The final polynomial is entirely ordinary: the powers and binomials below
describe meanings recovered from retained polynomial certificates.

## 1. The new front and frame

All source coordinates are unrestricted integers. The new affine front is

    t=8h,  d=t+2=8h+2,  R=F,  q=4z+1,  y=F(2v+1).

The existing growth request at index t is intended to recover F=d^t.
Neither t>=0 nor any other sign is assumed when orienting the Pell pairs.

The old square frame is an exact sum of 37 squares of actual affine bases,
indices and outputs, plus two. Its complete finite atom list is supplied
in `frame_certificate.json`. Make the four algebraically valid substitutions
t0=8h-16, d=8h+2, R=F and q=4z+1 in those atoms. The resulting 37 affine
forms use 33 distinct underlying coordinates. Denote them by u_1,...,u_33.
Define the new frame by the single quadratic row

    W=19+sum_(j=1)^33 u_j^2.                             (F)

The coordinates comprise x,y,F,B; the nine stored CRT representatives;
N; the stored semantic-anchor index; the fifteen outputs of power requests
3 through 17; the base BH_0; and the two affine parameters h,z. No private
Pell coordinate A,X_i,Y_i,comparison center, or norm witness occurs in
this list. Thus completeness can choose W after the arithmetic front and
before its private Pell witnesses, just as before.

Here is the exact elementary majorant used to prove all needed frame bounds.
For integers a,u,

    |a u| <= u^2+floor(a^2/4).

Indeed the minimum of u^2-a u on the integers is -floor(a^2/4), and the
same fact applies to -a. Consequently, for any integer affine form
L=c+sum a_j u_j,

    |L| <= sum_(a_j!=0) u_j^2+|c|+sum floor(a_j^2/4).   (M)

The following list covers the only nontrivial transformed atoms:

| Actual atom | Bound beyond the coordinate squares |
| --- | ---: |
| t=8h | 16 |
| t+1=8h+1 | 17 |
| R+t=F+8h | 16 |
| d=8h+2 | 18 |
| q=4z+1 | 5 |
| q+1=4z+2 | 6 |
| Any stored coordinate plus one | 1 |
| Any bare coordinate | 0 |

Every number in the third term of (M) is exact and is checked against the
literal 37-atom ledger. Since the maximum is 18, (F) implies

    W>=19,                 |every requested atom|<W.   (B)

It does not assert the stronger and unnecessary inequality atom^2<W.
All uses below require only the absolute-value bounds (B).

## 2. The large signed Pell center

Retain the odd frame norm

    A^2-W^3(W+2)(2a+1)^2=1.

It is the usual Pell equation at center W+1 with nonzero ordinate
W(2a+1). Classification gives |A|=X_l(W+1), and reduction of the ordinate
modulo W gives W|l. Since l>0, l>=W. Hence

    |A|>=X_W(W+1)>W^W,       |A-1|>4W^3.              (G)

The last inequality follows already for W>=5, and (B) gives W>=19.
This argument uses no arithmetic sign and no power interpretation.

## 3. The changed orientation pool

Let H be the actual semantic-anchor index, C its ordinate, and write the
principal ordinate errors as e_i=Y_i-k_i. In the source the pair at t is
`index0`, the pair at R+t is `index2`, and the derived semantic-anchor pair
is a different retained pair. Replace only the summand

    e_(R+t)^2 = (Y_(R+t)-R-t)^2

by

    (e_(R+t)-e_t)^2 = (Y_(R+t)-Y_t-R)^2.              (D)

The summand e_t^2 and every abscissa error (X_i-1)^2 remain. Thus the
new nonnegative quadratic form has the same zero set as the old error
sum: first e_t=0, then (D)=0 forces e_(R+t)=0. The replacement is an
invertible integral change of basis in the two error coordinates.

The squared cap still gives C!=0 and |C|>|H|. Handle |C|=1 first, without
applying a comparison-index theorem at that exceptional value. The cap
then forces H=0 and every other ordinate zero. The classified anchor index
is one, every other classified index is zero, and the retained anchor
ordinate error has small residue +1 or -1. Hence the reduced orientation
sum is strictly positive. The bound below makes it smaller than |A-1|,
contradicting its divisibility. Therefore |C|>1.

For |C|>1, the inherited signed-anchor comparison yields H!=0 and the
classified anchor index |H|; every other classified index is less than
|H|. By (B) all classified indices j_i are less than W. Reduction modulo
A-1 has abscissa residues s_i in {-1,1} and ordinate residues r_i with
|r_i|=j_i (or zero at index zero). This remains true for either sign of A.

For each unchanged ordinate error, |r_i-k_i|<2W. In the changed summand,
the two nominal indices differ by R=F, so the small error is

    r_(R+t)-r_t-F,

whose absolute value is less than 3W by (B). Every abscissa error has
absolute value at most two. For m<=15 principal pairs, the reduced sum E
therefore satisfies

    0<=E<(4m+5)W^2+4m<=65W^2+60<4W^3<|A-1|.         (P)

The strict middle inequality holds for W>=19. It is also valid in the
exceptional |C|=1 branch, because all its classified indices are below W.
The pooled congruence makes A-1 divide E, so E=0. In the ordinary branch
every unchanged error vanishes; e_t=0 and the difference error then
recover the missing e_(R+t)=0. Consequently both coordinates of every
principal pair have their exact signed Pell-polynomial values.

This establishes the complete orientation step before any arithmetic sign.
The finite source checker binds (D) to the exact old pool, including the
retained t and anchor terms. It also verifies every atom bound in (M).

## 4. Recovering a positive horizon

For every integer h the affine base d=8h+2 satisfies |d|>=2. The now
canonical signed-base power certificate is therefore applicable. If t<0,
its inverse congruence, together with (B) and (G), would force the exact
integer equality F*d^(-t)=1, which is impossible. Hence t>=0 and F=d^t.

If t=0, then F=1 and y=2v+1 is odd, with no sign yet asserted. The two
unchanged beta endpoints become

    x=2+(y+1)u_0,           x=1+(y+1)u_t.

Subtracting gives 1=(y+1)(u_t-u_0), an even number, a contradiction.
Thus t>0. Since 8|t, it follows that t>=8, d=t+2>0, and

    F=(t+2)^t>=10^8.

The signed-radix and affine-beta proof now applies: from q=4z+1 and the
canonical requests it first recovers the genuine nonnegative representatives,
then x>0 and |q|>=3, then y>=F. The endpoints consequently give

    x>=F+1,             x>=2+(t+1)y>=2+(t+1)F.        (E)

The binomial digit is decoded using |q| before asserting B or q positive;
it eventually yields B=binom(F+t,t)>0 and then q>0. The horizon proof does
not use these later conclusions as premises.

## 5. All growth thresholds for t>=8

Three elementary inequalities replace the predecessor's conservative
F>2^32 shortcut:

    F>(t+1)^t,        F>ell=2^22,
    x>=2+9*10^8>2^29.                                 (T)

The first follows from the strictly larger base t+2. The second and third
follow from t>=8, F>=10^8 and (E).

For the local-polynomial degree bound E0=2^23, (T) suffices to prove

    (2x)^E0 < 2^x.

Indeed, choose s>=29 with 2^s<=x<2^(s+1). Then
(2x)^E0<2^(E0(s+2)). The inequality E0(s+2)<2^s holds at s=29 because
2^23*31<2^29, and induction preserves it: s+3<2(s+2). Therefore
E0(s+2)<2^s<=x, as required.

The linear selector requires F>L_t^2, where L_t=lcm(1,...,t). At the
single small permitted horizon t=8,

    L_8^2=840^2=705600<100000000=F.

Every other positive multiple of eight satisfies t>=16. The independent
elementary bound L_t<=4^(t-1) then gives

    L_t^2<=16^(t-1)<(t+2)^t=F.

All further inherited numerical premises hold: t>=2; F>=7 for the
binomial-digit estimate F^2+F<=2^(F-1); (t-1)F>t for the local-size
majorant; x>ell(t+1) from (E); and all lower range indices t,t+1,y+1,x
are at most x. Thus no unverified t>=16 or F>2^32 premise is reused.

## 6. Completeness and independence of the frame

Pad any finite C222 refutation to a sufficiently large positive multiple
of eight. Define d=t+2 and F=d^t. Since d is even, v_2(F)>=t>v_2(t!).
Choose the odd multiplier 2v+1 sufficiently large, divisible by the odd
part of t!, and large enough that y=F(2v+1) exceeds every accumulator.
This gives the same even multiple of t! needed for the pairwise coprime
beta moduli. Choose an even beta code x in its CRT class.

Set R=F and B=binom(F+t,t). The selector theorem applies by Section 5,
and B is odd because v_2(F)>=t makes v_2(F+i)=v_2(i) for 1<=i<=t.
The inherited CRT parity pattern makes H_0 odd and the semantic anchor
even and dominant. Thus q=(BH_0)^x is 1 modulo four, giving z=(q-1)/4.
All true arithmetic outputs and the 33 underlying coordinates are now
fixed. Define W by (F), and only then choose the Pell frame and anchor
witnesses. The frame has no private Pell dependency.

Canonical principal pairs make each original ordinate and abscissa error
divisible by A-1. Their difference is likewise divisible, so the new pool
has an integer quotient. All original norm, cap, comparison and arithmetic
witnesses are therefore available. Conversely, Sections 1-5 recover their
required semantics from any new zero, so the retained C222/refutation
calibration applies.

## 7. Final exact algebra and achieved equations

After the semantic changes, the finite producer applies the inherited
eighteen Horn factorizations, integral monic projections, coordinate
translations and affine-exposure certificates. The new final row operation
is ordinary integer subtraction of one residual from another. It cancels
a repeated 64*h^2 coefficient between the growth-modulus and orientation
rows. Its explicit certificate preserves the entire simultaneous zero set.

The balanced endpoint has 238 unrestricted integer variables, 174
quadratic residuals, 5479 collected quartic monomials and height 7968.
The dimension endpoint has 237 variables, 173 residuals, 14129 monomials
and the same height. Both have exact degree four and maximum residual
coefficient 64. These are measurements of the delivered literal arrays.
They are not global minimality claims.

The semantic proof, followed by the exact finite maps, shows that each
equation has an integer zero exactly when a finite C222 refutation exists.
Composing the retained named C222/ZF/ZFC calibration gives the requested
ZFC-provable equivalence between integer unsolvability and Con(ZFC).
No new end-to-end proof-assistant development or consistency proof is claimed.
