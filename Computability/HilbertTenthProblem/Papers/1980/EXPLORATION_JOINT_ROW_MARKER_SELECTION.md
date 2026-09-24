# Joint row length and selection with seven Boolean words

A joint conditional component certifies both a single marker in every
row and its product with a selector bit using **ten operations and seven
Boolean words**. The ordinary two-gadget construction, after sharing its
radix quotient and boundary word, uses the same ten operations but nine
Boolean words. The saving here is two words sent to the eventual packed
mask. No minimum-count or complete tag-machine bound is claimed.

The component includes any fixed amount of padding below the row
boundary at the same cost. Its arithmetic is ordinary integer arithmetic;
no digitwise product is treated as a free operation.

## 1. Exact interface

Fix a numeral C=3^k with k>=1. Let R=3^m, m>=k, let there be t>=1 rows,
and put B=R^t and H=(B-1)/(R-1). Supply A with the paid equality CA=R,
so A=3^b with b=m-k. All seven words

    Q0,Q1,S0,S1,M0,M1,Qguard

are nonnegative Boolean ternary words below B. Impose

    S0+S1=H,
    2Q0+S0=M0,  2Q1+S1=M1,
    Qguard=Q0+Q1+AH,
    M0+M1=L.                                             (J)

No Boolean mask on L or Q0+Q1 is assumed. Then each row j has a unique
selector s_j in {0,1} and a unique position p_j in {0,...,b}, and

    S0_j=s_j,             S1_j=1-s_j,
    L_j=3^p_j,
    M0_j=s_j L_j,         M1_j=(1-s_j)L_j,
    Q0_j=s_j(L_j-1)/2,    Q1_j=(1-s_j)(L_j-1)/2.           (1)

Thus L and Q0+Q1 are themselves Boolean, every length is a single power
of three, and L_j<=R/C. Conversely every choice in (1) gives exactly one
tuple satisfying (J), with Qguard determined by its equation.

The labels 0 and 1 can be exchanged. For a tag production selected by
S1, use M1 as the selected length word.

## 2. The shared guard excludes the first crossing

The head equation has coefficients at most two, so S0,S1 partition the
row heads without carries. Initially both equations 2Qi+Si=Mi have zero
incoming ternary carry. Assume this remains true on entering a row;
it is enough to prove it on exit and proceed by induction.

Exactly one channel has a selector one at this row head. In the other
channel, a first nonzero digit of Qi would produce a digit two in Mi.
Hence that channel stays zero throughout the row. In the active channel,
the initial run of ones of Qi propagates the carry started by its head
selector. At the first zero, the carry produces the single marker one
in Mi and stops. Any later nonzero digit of Qi would again produce a
digit two, so there are no later ones.

This discussion also proves there is no incoming carry in the sum
Q0+Q1+AH within the row before the guarded position. Only one Qi can be
active, its digits are zero or one, and AH has no digit below position b.
If the active interval reached that position, its one plus the guard's
one would give the forbidden digit two in Qguard. It must therefore end
at some position p<=b. Both channel carries have stopped by then and
remain zero through the end of the row. The guard addition also has no
outgoing carry. This establishes the induction without assuming that
Q0+Q1 was already Boolean.

Consequently the two marker words never overlap: exactly one channel
contains a marker in every row. Their sum L is a Boolean one-marker
word, and their interval sum is the Boolean prefix below that marker.
These are conclusions, not extra masks. The argument includes b=0:
then both intervals are zero and the active marker lies at the row head.

For the converse, the two intervals in (1) are disjoint and vanish at
the guard position. All seven words are Boolean, every equation holds
rowwise with no carries, and every word lies below B. Marker positions
at a head, selection of only one channel, and arbitrarily many zero
auxiliary rows are all allowed.

## 3. Exact arithmetic and comparison with separate gadgets

With R,H and their stated geometry already available, use

    radix=C*A; guard=A*H;
    Qsum=Q0+Q1; Qguard=Qsum+guard;
    headsum=S0+S1;
    twiceQ0=2*Q0; marker0=twiceQ0+S0;
    twiceQ1=2*Q1; marker1=twiceQ1+S1;
    lengthsum=M0+M1.

The free comparisons are radix=R, headsum=H, marker0=M0, marker1=M1,
and lengthsum=L. There are exactly **four multiplications and six
additions**. Qguard is a computed word sent to the mask. If A is already
available, the incremental cost is nine. If both A and AH are already
available, it is eight. Neither division by the fixed C nor formation of
the guard is silently free in the stated ten-operation count.

For comparison, separately certify a full length marker using

    2Qfull+H=L, Qfull_guard=Qfull+AH

and certify a selected marker using the original projection gadget and
M0+M1=L. Sharing CA=R and AH gives ten operations in total. Its distinct
mask words are

    Qfull,Qfull_guard,L,Qselected,Qselected_guard,S0,S1,M0,M1.

The joint construction needs seven. Under a surrounding ordinary Horner
concatenation, removing two fields would remove two multiplication/addition
steps, but no such whole-system saving is claimed before the scale, field
bounds, positivity and remaining history equations have been supplied.

All-zero auxiliary words are a real issue for a positive-unknown system.
For example, markers always at the row head give Q0=Q1=0; selecting one
channel exclusively makes the other selector and marker words zero.
The present theorem is explicitly nonnegative. Positive adapters, fixed
forced rows, or another justified treatment must be paid in a complete
construction. No converse silently excludes these cases.

## 4. Small failures and useful conditional integrations

The shared guard is essential to this proof. At R=9 with two rows,
Q0=4,Q1=0,S0=1,S1=9 gives M0=M1=9. All six channel words are Boolean,
but one marker has crossed the row boundary; Qguard=34 is not Boolean.

Nor can one omit only the mask on Q0: Q0=6,Q1=0,S0=1,S1=9 gives
M0=13,M1=9 and Qguard=36, with every other word Boolean. Finally, at
R=9 with one row, Q0=0,Q1=1,S0=1,S1=0 gives M0=1,M1=2,Qguard=4.
Omitting the M1 mask admits this tuple even if L=M0+M1=3 is separately
known to be one-hot: M0 is the wrong selected length. These are scoped
omission examples, not an optimality proof over all encodings.

The computed Qsum is the exact prefix interval below L. Therefore adding
Boolean words N,Nbar with N+Nbar=Qsum costs one addition and two mask
words and gives a Boolean content word whose row value is below L_j.
This integration still needs its own positive adapters and row bounds.

The companion `../verification/explore_joint_row_marker_selection.py`
checks the ten-step DAG against five fresh symbolic residuals. It
enumerates all Boolean Q0,Q1 and all head partitions in its stated small
dimensions, derives both marker words and the shared guard, and filters
only the seven stated masks. Neither L nor Qsum is filtered. Every
accepted tuple is checked against (1), and every converse choice,
including zero channels and head markers, is separately reconstructed
and evaluated through the DAG. Its receipt states the exact finite scope.
