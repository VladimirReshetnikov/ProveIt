# A 67-operation marked three-cell halting-instance certificate

Using three-cell constraints on center, right, and next removes the
backward spatial shift from the local arithmetic. Combined with the
homogeneous one-hot compiler, this gives **67=38M+29A**, 27 strictly
positive unknowns, and 17 equations for each effectively compiled
Turing-machine halting instance.

The fixed numerals encode both the machine and its finite input. This is
an encoded-instance theorem, not a replacement for the89-operation
universal certificate whose machine index is fixed before the raw
integer input varies. Free numerals are used exactly as prescribed by
the operation-count measure.

The [checker](../verification/explore_three_cell_marked.py) and
[receipt](../verification/explore_three_cell_marked.json) contain all
67 source operations and residual checks. The computational reduction
uses the [exact-period three-cell lift](EXPLORATION_THREE_CELL_PERIOD_LIFT.md).
The proof below adapts the complete
[homogeneous marked70 system](EXPLORATION_HOMOGENEOUS_MARKED_CYCLIC_70.md).

## 1. Homogeneous compilation of a ternary relation

Fix an alphabet of `k>=1` symbols with marker0, and a relation
`R3 subset Alphabet^3` on center, right, and next. Give each site `k`
Boolean state indicators. Choose a fixed power of two `A>max(2k,4)`.
Use the following linear clause values and masks in separate radix-A
digits:

* Three at-most-one clauses: the occupancy of each site, mask `A-2`.
* Two occupancy equalities: center+right and center+next, mask1.
* For every forbidden triple `(a,b,c)`, the value
  `z_Ca+z_Rb+2z_Yc`, mask4.

The last value belongs to `[0,4]`. It has bit2 set exactly when all
three selected indicators are1. Weight2 on the next indicator makes
this test homogeneous; it introduces no constant guard. Every raw clause
value is below `A`, including occupancy sums before at-most-one recovery.
Thus the sum of weighted clause digits has no carries:

    phi=sum_(s,i) c_si*z_si, mu=sum_j A^j*mu_j.          (1)

All coefficients are positive because every bit occurs in its site's
at-most-one clause. As before, put `m=popcount(mu)` and append
zero-expression, mask1 clauses when necessary to make `m>=k`. They
do not change the relation.

Choose the fixed inner and outer radices and coefficients

    R>=max(2m sum c_si,2mu)+2, a power of two,
    p=k-1, H=k+m-2, B=R^(H+1)=2^d,
    Ccell=2 sum_(j<m) z_j R^j,
    Ds=sum_(i<k)c_si R^(p-i), s in {C,R,Y},
    MC=B-1-2 sum_(j<m)R^j, MF=2mu R^p.                 (2)

The first `k` bits are genuine indicators; the others are ignored
dummies. The same coefficient-mass proof as for homogeneous70 gives

    Fcell=DC*Ccell+DR*Rcell+DY*Ycell,
    0<=Fcell<=B-2,
    Fcell AND MF=0 iff all clauses pass,
    0<DC,DR,DY<B, 0<MC,MF<=B-2,
    MC odd, MF even, popcount(MC)+popcount(MF)=d.        (3)

At the inner target digit, the scalar field is exactly `2phi`. Every
off-diagonal coefficient is nonnegative and at most `R-2`; dummy
contributions occur strictly above the target. This proves (3) even
for typed bit tuples with zero or multiple genuine indicators.
The resulting `B` is at least16.

## 2. Three-cell cyclic transport needs only five operations

In decoded geometry `q=B^N`, `P=B^h`, with `1<=h<=N`, set
`D=q-1`, `J=D/(B-1)`. For the encoded word `C`, the right and next
words have digits at indices `i-h` and `i-h-1`. Write

    Rword=PC-kR*D, Yword=BPC-kY*D,
    Factual=DC*C+DR*Rword+DY*Yword.                     (4)

Both wrap quotients are nonnegative. With the fixed numeral
`E=DR+B*DY`, the exact local equation is

    (DC+E*P)C=F+z(q-1),
    z=DR*kR+DY*kY.                                     (5)

The five operations are `E*P`, `+DC`, `*C`, `z(q-1)`, and `+F`, giving
`3M+2A`. There is no backward shift and no multiplication of `F` by P.

For a genuine word, every state cell is at least2. Hence `C>=2J`, and

    kY=floor(BPC/D)>=2P,
    z>=2*DY*P>0.                                       (6)

Thus the quotient is strictly positive, with no sign adapter.

## 3. Complete equations and ledger

Supply the same27 positive unknowns as in homogeneous70:

    q,P,C,v,J,align,F,alpha,z,T,
    a,c,d,f,h0,i,j,k,o,r,s,w,tau,eta,zeta,gamma,yaux.

Use the unchanged counted packing

    Lambda=q^2, D0=q^3, S=C+qF, M=(MC+q*MF)J.

The seven outer equations are

    (B-1)J=q-1, Pv=q, (B-1)align=P-1,
    C+alpha=q,
    (DC+E*P)C=F+z(q-1),
    r=(Lambda-S)(Lambda-1)+M,
    C=2+B*T.                                            (7)

The ten kernel equations and their43-operation schedule are identical
to the homogeneous70 source. In particular, they use `X=wD0`,
`Yp=sD0`, `Delta=a^2+4a+3`, and `u=jc-(2r+1)`, with the full first,
main, rank, and fixed-minus auxiliary Pell equations. The checker states
their residuals alongside (7) and verifies the preceding-norm correction
in the auxiliary equation. No extra condition is omitted from the count.

| Part | M | A | Total |
|---|---:|---:|---:|
| Geometry |3|2|5|
| Low-field bound |0|1|1|
| Three-cell local equation |3|2|5|
| Powers and inverse packing |6|5|11|
| Unit marker |1|1|2|
| Outer subtotal |13|11|24|
| Full fixed-minus Pell kernel |25|18|43|
| **Complete marked source** |**38**|**29**|**67**|

## 4. Soundness in the required order

The same pre-power argument applies unchanged. The explicit bound gives
`0<C<q`, geometry gives `q>=P>=B>=16`, and the mask ranges in (3) give
`0<M<q^2-1`. Positivity of r then forces `0<F<q`, `0<S<q^2`, and
`q^2<=r<q^4`. These estimates justify the retained kernel directly at
the initially nonsquare scale `D0=q^3`.

It follows that `q` and `P` are powers of two. Their repunit and
alignment equations force `q=B^N` and `P=B^h`, `1<=h<=N`. The kernel also
gives `q^3 | binom(2r,r)`. Exact mask balance makes the inverse-packing
upper population threshold `3dN=log2(q^3)`, so the two recovered masks are

    C AND (MC*J)=0, F AND (MF*J)=0.                     (8)

After typing C, form its actual cyclic neighbors and the field (4).
It satisfies `0<Factual<q-1`: the upper bound follows cell by cell from
(3), and the lower bound follows from `DC*C>0`, before genuine occupancy
is known. Equation (5) now gives `F=Factual mod(q-1)`. Together with
`0<F<q`, this forces exact equality.

The field mask therefore enforces all homogeneous clauses at every cell.
Their occupancies satisfy

    n_i in {0,1}, n_i=n_(i-h)=n_(i-h-1).

The two consecutive shifts imply invariance under1, so all occupancies
are equal. The last equation of (7) fixes the unit cell to2, with the
genuine marker indicator1 and all dummy bits0. Consequently every
occupancy is1. The forbidden-triple clauses now give exactly `R3` on
the genuine alphabet at every cyclic cell. This proves marked cyclic
soundness, including exclusion of locally valid empty configurations.

## 5. Positive completeness and the halting theorem

For a marked cyclic configuration, rotate its marker to index zero,
assign dummy bits zero, and repeat a length-one word if needed. This
gives `N>=2` and a positive marker tail `(C-2)/B`. The canonical geometry,
field, and bound coordinates are positive; (6) proves the transport
quotient positive. All seven outer equations hold.

The masks vanish on this word. The actual packed r therefore has
population `3dN`, gives the required central-binomial divisibility,
and obeys the retained bounds. It is odd because C and q are even,
while MC and J are odd. The complete fresh positive Pell construction
in the homogeneous70 and generic cyclic proofs applies at this actual
`r,D0`, supplying all seventeen kernel unknowns and all ten equations.

The three-cell period lift associates to each marked3-by-3 TM tableau
an alphabet of valid3-by-3 blocks. Overlap of center/right and center/next
blocks gives precisely a three-cell relation. The block lift and center
projection are inverse and preserve the entire period lattice. Stronger
blank margins and at least three rows make the block around the original
boundary intersection one fixed marker, independent of the particular
halting run. The independent width and height padding theorem survives.

Thus halting yields marked `(h+1)`-by-`h` tori and hence cyclic witnesses
for (7). Conversely, any cyclic solution pulls back by
`a(x,t)=state(C_(-hx-(h+1)t mod N))` to a marked periodic block
configuration, whose center projection is a marked original tableau.
The original initialization, no-escape, and last-row conditions force
a genuine halt on the compiled input.

Every step is effective. The alphabet and all large fixed numerals
depend on the machine and input; the67-operation count includes the
marker and full positive arithmetic certificate but not a fixed raw-input
connection. No full enormous packed Pell tuple is numerically materialized.

## 6. Verification and independent review

Independent complete scoped mathematical/source review passes for both
positive directions, including the weighted forbidden-triple test, the
positive field before occupancy recovery, the connected occupancy
propagation, the positive quotient, and all retained Pell obligations.
Fresh author and independent default runs reproduce the saved receipt.
Every one of the67 primitives and17 residuals is checked, including the
preceding-norm correction at residual15.

The checker covers1,568 scalar cases and3,348 cyclic cases across empty
and full relations, a directional copy rule and a binary exclusive-or
rule. These include94 marked configurations and84 complete positive
marked outer tuples at length at least2. Four additional directional
checks distinguish the correct shifts at a nonconstant two-cell word.
There are71 positive dummy-only words and247 locally valid unmarked
words; the actual marker excludes them. Twelve zero-expression padding
clauses are exercised at alphabet size32, and length-one repetition is
checked separately.

A [separate independent audit](../verification/audit_three_cell_marked.py)
directly evaluates every one of the256 binary ternary relations on every
genuine indicator assignment and both zero/full dummy fillings. All
32,768 cases pass. Its [receipt](../verification/audit_three_cell_marked.json)
records unchanged hashes of the reviewed proof, source and main receipt.
This independently evaluates truth rather than calling the candidate's
scalar-truth helper; it uses the candidate's compiled coefficients.
