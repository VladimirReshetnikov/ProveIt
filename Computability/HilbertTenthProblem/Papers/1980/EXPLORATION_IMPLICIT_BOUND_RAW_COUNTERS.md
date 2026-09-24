# The raw counter bound is implied: 74, 75, and 76 operations

The aggregate bound in the parity-aligned raw counter systems is
redundant. Removing its positive slack and two additions gives complete
history certificates with the following counts.

| Registers | Operations | Products | Additions/subtractions | Positive unknowns | Equations |
|---|---:|---:|---:|---:|---:|
| One | 74 | 37 | 37 | 30 | 20 |
| Two | 75 | 38 | 37 | 31 | 21 |
| Three | 76 | 39 | 37 | 31 | 21 |

The semantics remain exactly those of
`EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md`: initial ordinary values
[2x,0,...,0], with x+x charged; all counters nonnegative; every update
+1 or -1; all final values zero; and the first counter's first step plus.
Program constraints are still separate. These are counter components,
and do not improve the universal bound of 90 by themselves.

The new source and schedules are in
`../verification/explore_implicit_bound_raw_counters.py/.json`.
The proof below establishes an exact positive-witness extension back to
the frozen 76/77/78 systems. In particular it does not use the old bound
to decode a field, or assume the old safe packing window in order to
prove that window.

## 1. Exact deletion and retained equations

Delete the positive unknown alpha and its equation

    F0+F1+alpha=q+J.

Delete the two evaluated additions S+alpha and q+J, where S=F0+F1.
The addition computing S remains because it is used in A=S-2J.
Every other equation and supplied unknown is unchanged. For k>=2 the
retained outer equations, apart from r=P, are

    q=2J+1, q=Wv, W=R^k, H(R-1)=2J,
    I=2x, I+alphaI=R,
    FKplus+FKminus=2J+H, 3T=2J+H,
    G0=F0+T, G1=F1+T,
    W(A+delta)=A-I,

where A=F0+F1-2J and delta=FKplus-FKminus. I is computed as x+x;
it is not another supplied unknown. For k=1, R means W: no R unknown,
power equation W=R, or redundant multiplication is introduced.

The six-field word and scale remain

    P=FKplus+qG0+q^2F0+q^3G1+q^4F1+q^5FKminus,
    r=P, D0=q^6.

All ten equations of the general-scale fixed plus-sign 43-operation
kernel remain. Its soundness is independent of index parity. The
exponent k is fixed and R^k uses the specified multiplication chain.

## 2. Preliminary bounds without digit assumptions

The input equation gives R>=3. Since q is odd and W divides q, W is
odd; R divides W and q and is odd as well. Also W>=R>=3. The time
equation is the integer identity

    I+(W-1)A+W delta=0.

Here I is even, so delta is even. The flag-sum equation implies
delta=H modulo two; hence H is even and H>=2. Therefore

    q-1=H(R-1)>=2(R-1), so q>R.

The odd integer q/R is at least three. In particular q>=9 and J>=4.
These deductions precede power recovery and use no ternary typing.

The retained head and top-mask equations give

    H<=J, 0<T<=J, 0<FKplus,FKminus<3J.

Thus delta>=-3J+2. The time equation and I>=2 give

    A=(-W delta-I)/(W-1)
      <=[W(3J-2)-2]/(W-1)
      <=9J/2-4.

For the last inequality use W>=3 and 3J-4>0. Consequently

    S<=13J/2-4,
    F0,F1<=13J/2-5,
    G0,G1<=15J/2-5.                              (1)

These bounds are weaker than the deleted one. They are sufficient to
start the kernel, but they must not be substituted into the predecessor's
native-field proof without a new carry argument.

Normalize the six positive fields in base q and let c_i be the carry
from field i-1 into field i, with c_0=0 and c_6 the overflow beyond P.
The bounds above give successively

    c_1<=1, c_2<=3, c_3<=3, c_4<=3, c_5<=3, c_6<=1.

For example G0+c_1<=15J/2-4<4q and
F0+c_2<=13J/2-2<4q. The analogous bounds handle G1,F1, and finally
FKminus+c_5<=3J+2<2q. This proves

    q^5<P<2q^6.                                 (2)

All fields are positive, so the lower inequality is strict. With q>=9,
(2) gives every general-scale kernel hypothesis:
D0>=81, r>=27, r<2D0, and D0<r^2. The kernel therefore recovers q as
a power of three and D0 dividing binomial(2r,r). No parity or preliminary
native-field assumption has been used.

## 3. The possible overflow is excluded by the carry valuation

Write q=3^ell, L=q^6=3^N, N=6ell. We know ell>=2, P<2L, and the
number of ternary carries in P+P is at least N. Suppose P>=L.
Its leading ternary digit is one, at position N. Among the N+1 possible
carry positions at most one can fail to carry. The leading position must
carry: if its incoming carry were zero, both it and the preceding
position would fail.

The highest ell-digit q-chunk below L has value at least J. To see this,
if all its positions carry, all their digits are at least one. If its
one possible failed carry occurs within the chunk, it cannot be the last
position. A zero digit causing that failure must be followed immediately
by a two to restart. Relative to the all-ones repunit, this replaces
3^j+3^(j+1) by 2*3^(j+1), increasing the value by 2*3^j. If the failed
position instead has digit one with zero incoming carry, the following
two also only increases the repunit value. All other positions have
digits at least one. In every case the chunk is at least J.

In the base-q normalization this chunk equals FKminus+c_5-q. Hence

    FKminus+c_5>=q+J.

Since FKplus+FKminus<=3J and q=2J+1, this gives

    0<FKplus<=c_5-1<=2.                          (3)

If FKplus=1, the first two ternary digits of P are 1,0, giving two
failed carries. If FKplus=2 and q>=27, its first three digits are 2,0,0;
the latter two positions both fail to carry. Both contradict the bound
of at most one failure. These digits really are the initial digits of
P, since all later fields are multiples of q.

The remaining case is q=9 and FKplus=2. Then J=4, H<=4 and delta>=-8.
Thus A<=[8W-2]/(W-1)<=11, so S<=19, F_i<=18, and G_i<=22.
Starting with c_1=0, these bounds give c_2,c_3,c_4,c_5<=2. Equation (3)
would then force FKplus<=1, again a contradiction. This handles q=9
without assuming any decoded counter value or complete frame.

It follows that P<L. The direct unit-two mask theorem now applies in its
ordinary range: P has unit digit two and all N ternary digits are one
or two. Each of its six normalized q-chunks therefore lies in [J,q-1].

## 4. The time equation excludes carries between the supplied fields

Let p_0,...,p_5 denote those normalized native chunks. First
FKplus<3J forces c_1=0: if FKplus>=q, its remainder would be at most
J-2, below a native chunk. Thus FKplus=p_0>=J, and

    delta=2(FKplus-J)-H>=-H.

The time equation consequently gives the much stronger bound

    A<WH/(W-1)
      =(q-1)W/[(R-1)(W-1)]
      <=3(q-1)/4.                               (4)

This bounds the actual signed computed A. It does not yet assume that
either raw numerical track F_i-J is nonnegative.

Put a=floor(F0/q) and b=floor(F1/q). By (1), 0<=a,b<=3. Write the
remainders as d0,d1, in [0,q-1]. The guard/base structure now controls
the carries exactly:

* In G0=F0+T, the carry c_2 is a. An additional carry would leave
  p_1=d0+T-q<=T-1<J, impossible.
* In F0+c_2, the carry c_3 is a. An additional carry would leave
  p_2=d0+a-q<=a-1<=2<J, impossible.
* In G1+c_3=F1+T+a, the carry c_4 is b+epsilon for epsilon in {0,1},
  since T+a<=J+3<q.
* In F1+c_4, the carry c_5 is b. An additional carry would leave
  p_4=d1+c_4-q<=c_4-1<=3<J, impossible.

Write p_2=J+u and p_4=J+v, with u,v>=0. Since d0=p_2-a and
d1=p_4-c_4, the actual aggregate is

    A=(a+b)(q-1)+u+v-epsilon.                    (5)

If a+b>=1, (5) gives A>=q-2. But q>=9 implies
q-2>=3(q-1)/4, contradicting (4). Hence a=b=0. An extra c_4=1 would
now leave the G1 chunk at most T-1<J, so epsilon=0 as well.
All intermediate carries vanish. The last flag also has no incoming
carry and P<L, so every one of the six supplied fields equals its
native normalized chunk.

This is the essential implication missing from a purely numerical
packing bound: any whole-q contribution hidden in a numerical field
would exceed what the exact time equation permits.

## 5. Restore the deleted bound and the complete history theorem

The now-native flag pair decodes to complementary Boolean head words.
The retained geometry recovers R=3^m, q=R^u and

    H=1+R+...+R^(u-1), T=(R/3)H.

As in the predecessor, native G_i=F_i+T forces F_i-J to have a zero
highest ternary digit in every R-block. At the first overlap, a native
two plus the top-mask one would produce a forbidden zero. The raw
aggregate A is therefore an ordinary sum of two Boolean tracks whose
block values lie between zero and R/3-1. In particular

    0<=A<=(R/3-1)H<=J, so S=2J+A<=3J.

Define alpha=q+J-S. It is an integer at least one and satisfies the
deleted equation. Every accepting solution of the new system thus has
a unique positive extension to the old system. Conversely, delete alpha
from any old solution. All remaining equations hold with exactly the
same supplied values, including r and every Pell auxiliary.

The predecessor's complete interpretation, parity-derived frame
alignment, first-plus condition, and positive converse now follow
unchanged. No new enormous Pell coordinates need to be constructed in
this witness correspondence. In particular no condition on complete
frames was silently used to prove the deleted bound.

## 6. Accounting and verification boundaries

The deletion removes one positive unknown, one equation, and exactly two
additions. The products and the raw input operation are unchanged.
The specified-chain count becomes 74+ell(k), with ell(1)=0 and the
single-register alias R=W. The explicit k=1,2,3 schedules give the table
above. Every retained source polynomial is unchanged; after the deletion,
the inherited acyclic norm correction is checked at its shifted index.

Independent full proof and source audits and fresh verification pass.
The new checker enumerates 52,116, 4,377, and 756 positive preliminary
tuples for the three register counts, respectively, without the deleted
bound or a native-field filter. Of these, 39,189, 2,895, and 486 violate
the old bound. None passes the complete mask in this small range; the
separate 15, 22, and 104 canonical full histories do pass and restore
the unique positive alpha. The standalone overflow lemma in
`EXPLORATION_RAW_ALPHA_OVERFLOW_LEMMA.md` has an independent full audit
and checks 29,520 overflow words, 14,591 highest-chunk cases, and 684
small-boundary cases. These finite receipts support the general proof
and do not replace it. The earlier bounded exploration in
`../verification/explore_raw_counter_alpha_bound.py/.json` checked
1,216,942 even-index candidates violating S<=3J and found none accepted.
That search used exact valuations without native-field or safe-window
filters, but covered only its stated finite power geometries. It was
evidence guiding this proof, not a substitute for Sections 2--5, and its
interrupted q=6561 run is explicitly excluded from its receipt.

The unconstrained endpoint relation still accepts every positive x.
A smaller universal certificate requires program restrictions and their
full counted connection to these histories.
