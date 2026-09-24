# A unique start state at the same67-operation cost

The [marked three-cell67 certificate](EXPLORATION_THREE_CELL_MARKED_67.md)
can require its start state to occur exactly once in the cyclic word,
without adding an operation. Pack the already computed positive marker
tail `Z=B*Tmarker=C-2` in the low mask field, and forbid the start bit
there. An extra ignored dummy position keeps the two mask populations
balanced. The resulting complete cyclic predicate still costs
**67=38M+29A**, with27 positive unknowns and17 equations.

The predicate here has a cyclic length `N>=2`. Repeating a length-one
marked word would duplicate its start and is not an allowed completeness
step. This result supplies a unique-start arithmetic component; it does
not itself prove a fixed raw-input halting reduction. Section6 separately
proves a conditional four-operation endpoint test.

The [checker](../verification/explore_unique_start_cyclic.py) and adjacent
[receipt](../verification/explore_unique_start_cyclic.json) contain the
full source and finite evidence.

## 1. The changed cell alphabet and masks

Fix an alphabet with `k>=2` symbols and any relation on center, right,
and next. Symbol0 is Start; when using Section6, symbol `k-1` is End.
Use exactly the homogeneous clauses of the preceding67 construction:
three at-most-one tests, two occupancy equalities, and a weighted
`(1,1,2)` mask4 clause for each forbidden triple. Write their linear
form and mask as

    phi=sum_(s,i)c_si*z_si, mu=sum_j A^j*mu_j,
    m=popcount(mu)>=k.

Zero-expression, mask1 padding gives `m>=k` when necessary. All `c_si`
are positive. Now permit **m+1** cell positions, numbered `0,...,m`;
the first k are genuine state indicators and the rest are ignored
dummies. Choose

    R>=max(2(m+1)sum c_si,2mu)+2, R a power of two,
    p=k-1, H=k+m-1, B=R^(k+m)=2^d,
    Ccell=2 sum_(j=0)^m z_j R^j,
    Ds=sum_(i<k)c_si R^(p-i), s in {C,R,Y},
    MC=B-1-2 sum_(j=1)^m R^j,
    MF=2mu R^p.                                      (1)

The state mask MC permits precisely positions1 through m and forbids
position0. It will test Z, not C. The local field still uses the full C
cells, including their genuine position0. The coefficient-mass bound
is now `2(m+1)sum c_si<=R-2`; the highest product degree is `k+m-1`.
Consequently, for every Boolean assignment to all m+1 positions,

    Fcell=DC*Ccell+DR*Rcell+DY*Ycell,
    0<=Fcell<=B-2,
    Fcell AND MF=0 iff the homogeneous clauses pass.   (2)

The target coefficient remains `2phi`, because every dummy position
is above `p`; there are no off-diagonal or between-cell carries.
Moreover

    0<DC,DR,DY<B, 0<MC,MF<=B-2,
    MC odd, MF even,
    popcount(MC)=d-m, popcount(MF)=m.                  (3)

The full encoded Start cell with dummy0 is still exactly2. A genuine
non-Start state may have any dummy bits but has its position0 unset.

## 2. Source change and exact predicate

Keep every supplied coordinate and every equation of marked67 except
the packed-index equation. Move the existing two instructions

    Z=B*Tmarker, marked_rhs=2+Z

before packing; their comparison is still `C=marked_rhs`. Set

    Lambda=q^2, D0=q^3, S=Z+qF,
    M=(MC+q*MF)J,
    r=(Lambda-S)(Lambda-1)+M.                         (4)

The other six outer equations remain

    (B-1)J=q-1, Pv=q, (B-1)align=P-1,
    C+alpha=q,
    (DC+(DR+B*DY)P)C=F+z(q-1),
    C=2+B*Tmarker.                                   (5)

Retain the identical ten fixed-minus Pell equations and43-operation
kernel. Replacing one operand in the packing and reordering two paid
instructions do not change the count: outer24 plus kernel43 is67,
or38M+29A. There remain27 positive unknowns and17 equations.

Pointwise in the supplied coordinates `q,P,C`, the exact represented
predicate is:

* `q=B^N, P=B^h`, with `N>=2, 1<=h<=N`;
* the C digits are genuine one-hot alphabet states with arbitrary
  permitted dummy bits;
* the unit cell is exactly Start with dummy0, and no other cell is Start;
* the fixed relation holds at every cyclic triple with offsets
  `0,-h,-h-1`.

Existentializing these coordinates gives the corresponding unique-start
cyclic existence statement. The source does not silently assert that an
arbitrary marked cyclic configuration can be made unique.

## 3. Bounds before decoding and exact typing afterward

In any positive solution, the marker equality and low-field bound give

    0<Z=C-2<C<q.

The mask bounds and repunit equation still give `0<M<q^2-1`.
Positivity of r then forces `Z+qF<=q^2`; as Z is positive, `F<q`.
Both fields are strictly below q, so `0<S<q^2`, and

    q^2<=r<q^4, D0=q^3<r^2.

The full retained kernel argument therefore applies in the same sound
order, giving `q=B^N`, `P=B^h`, and the central-binomial divisibility.
Balanced populations in (3), with the inverse-packing identity, recover

    Z AND (MC*J)=0, F AND (MF*J)=0.                    (6)

The exact equation `Z=B*Tmarker` makes Z's entire unit radix-B digit
zero. Adding2 therefore causes no carry: C's unit digit is exactly2,
and every other C digit is the corresponding Z digit. The first mask
in (6) types those other digits into positions1 through m. Thus every
cell has typed genuine and dummy bits, and Start's position0 is absent
everywhere except the unit cell.

Form the actual cyclic field from C. Its range is
`0<Factual<q-1`: the upper bound comes from (2), and the lower bound
uses `DC*C>0`, before genuine occupancy has been established. The
transport equation gives equality modulo `q-1`; together with
`0<F<q`, it forces `F=Factual`. The second mask now proves the local
clauses. Occupancy is at most1 and invariant under h and h+1; hence it
is constant. The unit Start has occupancy1, so every cell is a genuine
one-hot state. The forbidden-triple clauses prove the intended relation.
No other state can be Start because its position0 was forbidden.

Finally `N=1` is impossible: it would give `q=B`, while
`C=2+B*Tmarker>B` contradicts `C<q`. This proves the complete stated
unique-start predicate without an unpriced length condition.

## 4. Strictly positive completeness

Take any word satisfying the predicate in Section2. Its length is at
least2 and every cell after the unit cell has positive state code.
Thus `Tmarker=(C-2)/B` is a positive integer. Its low field Z is positive
and satisfies the first mask in (6); the local field satisfies the
second. Set all geometry and bound witnesses canonically.

Every genuine cell has value at least2, so `C>=2J`. The standard
right and next wrap quotients satisfy

    Rword=PC-kR(q-1), Yword=BPC-kY(q-1),
    kR>=0, kY>=2P.

Therefore the local transport coordinate

    z=DR*kR+DY*kY>=2*DY*P>0

is positive, and all outer equations hold. The actual packed index
has population `3dN`, supplies the central-binomial divisibility, and
is odd: Z and qF are even, MC and J are odd. The bounds above hold.
The retained fresh positive Pell construction at this actual r,D0
supplies all seventeen kernel coordinates. No new index is identified
numerically with a witness from the earlier packing.

## 5. Why the extra position costs no operation

Previously the state mask permitted m positions and the field mask
tested m bits. Forbidding the Start position would remove one permitted
position and raise the combined population, breaking the q^3 threshold.
The extra ignored position restores the number of permitted positions
to m. Its effects on R, B, the coefficient numerals and the masks are
all fixed at compilation time. The full local equation and packing
schedule use the same number of arithmetic operations.

## 6. Conditional endpoint pin in four operations

Give End the highest genuine position `k-1`, and define the fixed numeral

    CE=2R^(k-1).

Then `CE` divides B. Every dummy contribution is also divisible by CE.
For a genuine one-hot cell, divisibility of its entire scalar value by
CE holds **exactly** when the genuine state is End: any lower genuine
position contributes a nonzero residue `2R^s<CE` that the dummy terms
cannot cancel.

Suppose an independently established exponent interface gives
`W=B^j` for some `1<=j<N`. Introduce positive `L,beta,Tend` and impose

    C=L+CE*W*Tend, L+beta=W.                          (7)

The four operations are `CE*W`, multiplication by Tend, addition of L,
and `L+beta`. The two equations imply `0<L<W` and

    floor(C/W)=CE*Tend.

Because B is divisible by CE, divisibility of this quotient by CE is
equivalent to divisibility of its low digit. Thus (7) selects exactly
the End state at position j, including any permitted dummy bits.

Conversely, when that digit is End, take `L=C mod W`,
`beta=W-L`, `Tend=floor(C/W)/CE`. All three are positive: C has unit
digit2 and `j>=1`, so `0<L<W`, and the endpoint digit is nonzero.

Before any power interpretation, the positive equations (7) themselves
give `W<C<q`, since `CE>=2` and Tend is positive. Hence they supply the
strict upper bound required by the
[seventeen-operation exponent bridge](EXPLORATION_RAW_INPUT_EXPONENT_BRIDGE.md).
This preliminary implication is independent of endpoint decoding.

The pin lemma alone does not show that the selected End lies in the
same computation rectangle as Start. A fixed raw-input tableau
interface must still prove that fact. Nor does this note establish
that interface's initialization or halting semantics. These remain
separate from the complete unique-start cyclic certificate proved above.
