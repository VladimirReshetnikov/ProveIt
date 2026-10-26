# Affine horizons inside fixed-base power pools

## Result, logical scope, and attribution

Two literal quartics use **215 independently unrestricted integers and 152
quadratic residuals**. The sparse endpoint has 14,578 collected monomials and
height 16,866; the low-height endpoint has 34,700 monomials and height 4,512.
Every residual coefficient has magnitude at most 64. The ordinary proof below,
composed with the retained C222/ZF/ZFC calibration, establishes in ZFC that each
polynomial has an integer zero exactly when there is a finite syntactic ZFC
refutation. Negation is the stated equivalence with Con(ZFC). Neither
consistency nor nonsolvability is asserted separately.

The pinned immediate parent is Round21's `beta217/equation.json`, before its
optional row-basis choices. Its complete unchanged release is retained in
`inherited/Round21_Integer217.zip`; `sources/parent217.json` is its exact equation.
The inherited names are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The direct numerical C222
route uses neither a K215 execution nor Jones specialization.

Source160 already supplies the affine horizon t=8h, F=(t+2)^t, weak affine
majorants, difference orientation error, and the t=8 numerical estimates.
Source158 supplies fixed-base pooling and the shared-private-consumer method.
Source159 supplies the six inherited radical projections. These are credited
components, not rediscoveries. The new arithmetic compatibility argument is
that a fourfold Pell frame makes fixed-base pooling work with **absolute** atom
bounds rather than the old squared-atom bounds. This permits the credited
affine horizon in the pooled strict-range parent. The additional exact Horn
contraction specializes the credited consumer identity after earlier private
coordinates have already disappeared.

No new end-to-end Lean/Rocq compilation, encoded object-ZFC proof, global
minimum, or worldwide-priority assertion is made. Finite certificates certify
literal polynomial algebra, not the unbounded arithmetic argument.

## 1. Precise semantic changes and the new frame

In the pinned parent, actual t is coordinate 0, actual A is stored `shared.A`
plus 1, and the coordinate named y stores actual y+1. The initial power request
has actual base/index t and output F. Change its base, but not its index, to

    t=8h,       d=t+2=8h+2,       F=d^t.                 (1)

This replaces the old cofinal horizon t=16+h_old². The power equality in (1)
is only proof notation for the modified quadratic certificate. The literal
change is T_t -> T_d in its modulus row and the correction -2Y_t in its power
row. Substitute 8h for every occurrence of t and delete the old private
horizon-root coordinate and its row. This is a semantic zero-existence change,
not a pointwise map of all old witness tuples.

The 34 actual source atoms, plus the new base d, cover all bases, indices and
outputs of the **17** retained requests. After the substitution they are affine
forms in 43 distinct pre-Pell coordinates u_j. They include all fourteen pooled
outputs, t,F,F+t,x,y+1,B,N,q,q+1,BH, all actual CRT representatives, and the
actual derived semantic-anchor label J_anchor. In this chart the latter is

    a_stored+b+4u19+2u22+2u26+2u28+2u30+2u32
      +4u34+2u35+2u38+2u41+4u60+2u61.                 (2)

Names such as u19 in (2) refer to the original pinned 217-coordinate chart;
the complete final renumbering is supplied. No private Pell coordinate occurs
in this list. The new shared product introduced in Section 6 is not framed.

For every integer a,u, |au| <= u²+floor(a²/4). Hence for each affine atom
L=c+sum a_j u_j,

    |L| <= sum_(a_j!=0) u_j² + |c|+sum floor(a_j²/4).

The exact maxima in the atom ledger are 16 for t and F+t, 18 for d, 21 for
J_anchor, 5 for q=4z+1, and 6 for q+1. Bare coordinates have bound 0 and the
shifted representative a_stored-1 has bound 1. Therefore impose

    W = 22 + sum_(j=1)^43 u_j².                         (3)

Then W>=22 and **|every actual atom|<W**. We do not claim atom²<W. All 51
base/index/output ports of the seventeen requests are independently checked
against this ledger. The old frame was a unit combination of its defining row
and retained rows; its exact certificate is preserved. Replacing that one
row by (3) does not discard any independent Pell or orientation condition.

## 2. Fourfold Pell growth and orientation before arithmetic signs

Replace only the two frame multiplication rows by

    U=4W(2z_frame-1),       V=(4W+1)U,                  (4)

and retain A²+U²-V²=1. Put S_frame=4W. The nonzero ordinate U is a multiple
of S_frame. Pell classification at center S_frame+1 and the congruence
Y_l(S_frame+1)=l modulo S_frame give a nonzero index whose absolute value is
at least S_frame. Consequently

    |A| >= X_(S_frame)(S_frame+1) > S_frame^S_frame
         = (4W)^(4W),       |A-1|>4W³.                 (5)

No arithmetic sign or interpreted power was used. In completeness choose
index S_frame. The quotient Y_(S_frame)(S_frame+1)/S_frame is odd (equivalently
Y_(S_frame)(S_frame+1)=S_frame modulo 2S_frame); hence the integer z_frame in
(4) exists. This is the same odd Pell-frame completeness argument at the larger
integer S_frame. The center is chosen after the finite arithmetic front and W.

Keep every signed semantic-anchor norm, cap, and principal-pair condition.
In the orientation pool replace only

    (Y_(F+t)-F-t)²  by  (Y_(F+t)-Y_t-F)²,              (6)

retaining (Y_t-t)² and all abscissa errors. The two error systems have the same
zero set. This credited difference change is checked at the residual level,
including the previously subtracted norm rows and Pell-difference coordinates.

The inherited cap proof bounds classified indices by the actual anchor label,
whose absolute value is <W by (3). As in source160, handle |C_anchor|=1 first:
the cap forces the nominal anchor label to zero and the other ordinates to
zero; its anchor orientation error has residue +1 or -1. The reduced nonnegative
sum is nonzero, but smaller than |A-1|, contradicting divisibility. Thus the
comparison theorem is applied only after |C_anchor|>1. It gives the inherited
signed classified-index bound <W. Each unchanged ordinate error has absolute
small residue <2W; the changed error (6) has residue <3W, and each abscissa
error has residue at most 2. For at most fifteen principal pairs the reduced
nonnegative error E_orient satisfies

    0<=E_orient<65W²+60<4W³<|A-1|.                     (7)

The middle inequality holds for W>=22. Divisibility forces E_orient=0.
Every reduced original orientation error vanishes, including the removed one recovered using the
retained t-error. Thus every pair is the canonical signed Pell pair at its
signed nominal index. This remains valid for negative A. No positivity of t,
y, x, B, q, or the CRT representatives has been assumed.

## 3. Fixed-base pooling under weak atom bounds

This is the new compatibility estimate. Let r<=15, n be a nonzero integer,
and assume |n|,|m_i|,|k_i|<W, W>=22, with canonical signed pairs X_i,Y_i at A
and Z_i=AY_i. Retain the credited two-row block

    K-2H-(2A-n)L=0,       S-nK+L=0,
    H=sum Y_i(m_i-X_i),   S=sum[(m_i-X_i+Z_i)²-Y_i²].    (8)

These are quadratic rows; their names introduce no extra variables beyond K,L.
Put T=2An-n²-1. The complete identity

    sum(m_i-X_i+Z_i-nY_i)² = S-2nH-T sum Y_i²           (9)

holds modulo the retained AY rows. Thus T divides the left side. Since T=-1
modulo n, n is invertible modulo T, so the signed Pell power congruence is
valid even when k_i is negative.

Set b=W-1>=21. Multiplying by n^(2b) clears all negative indices and shows
that T divides the ordinary nonnegative integer

    E=sum[m_i n^b-n^(b+k_i)]².

For |n|>=2 each summand is at most 4b^(4b); the same estimate also covers
n=+/-1. Thus

    0<=E<=60b^(4b) < (4W)^(4W).

For example b<W and 60<4^(4W)W^4 prove the displayed strict inequality.
On the other hand,

    |T|>=2|A|-(W-1)²-1>|A|>(4W)^(4W).                 (10)

Therefore E=0. At nonunit n, every k_i>=0 and m_i=n^(k_i), since a negative
index would imply m_i n^(-k_i)=1. At n=+/-1 the signed unit value is exact,
with no claim that its index is nonnegative. The two pools have r=11 at q+1
and r=3 at q. The same estimate with r=1 validates each of the three retained
singleton congruences under the new weak frame; their former squared-frame
hypothesis is not silently reused.

Conversely genuine powers give each individual Pell error divisible by T;
(9) proves L=(S-2nH)/T integral, and K=2H+(2A-n)L supplies (8). The pool change
preserves zero existence; the quotient construction is not an arbitrary
preliminary-tuple inverse.

## 4. Horizon and signed-beta bootstrap, without circular positivity

The base d=8h+2 is always nonzero and nonunit. The singleton lemma therefore
forces t>=0 and F=d^t. If t=0, then F=1 and y=F(2v+1) is odd, of either sign.
The two endpoints become

    x=2+(y+1)u0,       x=1+(y+1)ut.

Their difference says 1=(y+1)(ut-u0), impossible because y+1 is even. Thus

    t>=8,       F=(t+2)^t>=10^8>1.                     (11)

Now use the prior Round21 bootstrap in its correct order. The affine radix
q=4z+1 is nonzero, and |q+1|>=2. Interpret the q+1 pool first. It gives genuine
nonnegative actual CRT representatives and derived label, with the anchor
excluding zero label. Hence H=2+sum representatives>=2. The raw row
B*mu=C+F+1 has positive right side, so B!=0 and |BH|>=2. The singleton request
q=(BH)^x gives x>=0. Since y is a nonzero multiple of F, if x=0 the endpoint
x=1+[1+(t+1)y]ut would make 1+(t+1)y divide -1, impossible for t>=8 and
|y|>=F>1. Hence x>=1 and |q|>=2. Only now apply the q pool: its y+1 index
forces y>=-1, whence the nonzero-multiple condition gives y>=F>0.

The first endpoint then forces u0>=0 and x>=F+1; the last forces ut>=1 and

    x>=2+(t+1)y>=2+(t+1)F.                             (12)

The inherited normalized remainder norm authenticates all short signed
remainders. Signed binomial recovery then gives B=binom(F+t,t)>0 and the
self-radix equality gives q>0. Nothing earlier assumes these last signs.

The exact smaller-threshold estimates are those proved in credited source160.
In particular F>ell=2^22 and x>=900000002>2^29. For the inherited local-degree
bound E0=2^23 and R0=2+t+x+y+F, (11)-(12) imply R0<2x. If
2^s<=x<2^(s+1), s>=29, then

    E0 log2(2x)<2^23(s+2)<2^s<=x.

The middle inequality holds at s=29 and persists by induction. Thus
R0^E0<2^x<N. We explicitly replace, rather than reuse, the false general
claim x>2^32 at the new smallest horizon. All derived-label coefficient
budgets use x>ell(t+1), which follows from F>ell and (12).

For the binomial selector radius R=F, at t=8 one has
lcm(1,...,8)²=840²=705600<10^8. Every other positive multiple of eight is at
least 16, so lcm(1,...,t)<=4^(t-1) gives Lambda_t²<=16^(t-1)<(t+2)^t=F.
The inherited all-primes CRT selector theorem therefore applies in both
directions. Labels satisfy the retained strict local bounds <t, and
F=(t+2)^t>t^t makes the inherited positive-coefficient multiplicity comparison
strict. The ordinary local-row, range, nonzero-boundary, positive-accumulator,
and Horn-closure arguments now apply. In particular y=F is excluded only
AFTER local-row recovery, as in the parent. A zero yields a finite refutation.

## 5. Completeness and every changed choice

Start with a finite C222 refutation and all its finitely many local parameters,
derived labels and truth-padding data. Choose a sufficiently large positive
multiple of eight t strictly beyond them and the proof-tree length. Put
F=(t+2)^t. Then v2(F)=t>v2(t!), so the inherited beta CRT construction supplies
arbitrarily large y=F*a² with a odd and divisible by the odd part of t!. This
satisfies the retained odd-linear condition with v=(a²-1)/2 and can dominate
every finite accumulator. All beta moduli are odd, permitting arbitrarily
large even x. Also v2(F+i)=v2(i), 1<=i<=t, so B=binom(F+t,t) is odd. The
parent's parity-prescribed representatives give odd H; q=(BH)^x is an odd
square and is 1 modulo 4, so its affine radix parameter exists.

Construct all genuine power outputs, normalized remainders and local/Horn
wires as in the parent. These determine all 43 framed coordinates before
private Pell choices. Set W by (3), choose the strong frame using (4), then
complete all canonical principal pairs and the semantic-anchor witnesses
with the inherited simultaneous construction. Nothing about that construction
requires the smaller frame value or the old cofinal square horizon, only the
explicit bounds and parity just proved. The converse of (8) gives all four
pool coordinates. Canonical Pell ordinate and abscissa errors are divisible by A-1;
the difference in (6) is therefore divisible by A-1, so the modified
squared-error congruence has an integral quotient. Section 6 supplies the shared product and final literal coordinates.
Thus every finite refutation yields a zero. Completeness is a fresh witness
construction, not a bijection preserving the old horizon or old F.

## 6. One more exact private-consumer contraction

Use the original 217-coordinate parent chart. Let F=x3, S=x12, Sp=x13,
a=x8, b=x9, s=x19, K=x62, p=x75, r=x76, g=x77, v=x78, e1=x79, e2=x80.
The defining rows include

    rK=K-FSp, rp=p-1-Fb, rr=r-1-F(a-1),
    rg=g-1+2F+2Fa+4Fb-2Fs.

Delete p,r and their rows. Add one integer Jprod with rJ=Jprod-FS. Replace
only the three consumers by

    C61=-Sp-Kb+gv+e1,
    C64=-S-Jprod(a-1)+v,
    C65=S+Jprod*b-Sp-K(2a+4b+2s)+e2.                    (13)

Writing R61,R64,R65 for the old consumers and D=2a+4b+2s, the full polynomial
identities, valid without assuming zeros, are

    C61=R61+Sp*rp-b*rK,
    C64=R64+S*rr-(a-1)*rJ,
    C65=R65+b*rJ+(8Sp-S)*rp+4Sp*rr+Sp*rg-D*rK.         (14)

No other retained row uses p or r. The forward map adjoins Jprod=FS and drops
p,r. The inverse restores p=1+Fb and r=1+F(a-1), drops Jprod, and leaves every
other coordinate fixed. The new product row makes these inverse on integer
zero sets. The retained rK,rg and identities (14) prove both implications.
All changes remain quadratic. This exact specialized composition is credited
to source158's more general private-wire construction; the prior joint-square
contraction and already eliminated third factor are not counted a second time.

The affine horizon removes one coordinate and row; this exact contraction
removes a further one. Therefore 217/154 becomes 215/152. Every subsequent
row operation is R_i<-R_i+kR_j, with i!=j, integer k, and inverse -k. The
complete frozen lists give two exact presentations of the same integer zero
set. Squaring and adding all rows gives the delivered ordinary quartics.

## 7. Artifact scope and comparisons

`build.py` reconstructs every new stage using only frozen operations.
`check.py`, which imports no producer, separately verifies every actual
power port and affine bound, the old frame identity, every semantic source
edit, private-root isolation, the complete ideal identities (14) and inverse
maps, every forward/inverse row operation, every collected coefficient,
metrics and liveness. Deliberately corrupted frame, growth and restoration
certificates must fail. Normal and optimized Python runs are supported.
`verify.py --parent` additionally checks and rebuilds the complete retained
Round21 parent; its retained Strict Horizons archive closes the inherited
arithmetic and named logical-source dependencies. No numerical zero search is
used or claimed.

The sparse215 endpoint improves the previous sparse217 point
(217/154/14615/16866) to 215/152/14578/16866. It also dominates the independently
inspected incoming Pooled Projection216 point (216/153/15158/334952) in all
four metrics. The low-height215 point lowers 4576 to 4512 versus the previous
low-height217 point but increases support from 25949 to 34700. Incoming
Quotient Carriers220 has lower height2336, so no global height frontier or
unqualified dominance claim is made.
