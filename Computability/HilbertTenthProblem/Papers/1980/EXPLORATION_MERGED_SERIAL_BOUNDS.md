# A shared positive bound and native adapter reuse: 119 operations

The serial labelled raw-counter composition can use one positive bound
for its zero-test mask and its program fields. Its program source-support
calculation also already computes one of the native adapters. Together
these changes give **119 operations: 56 multiplications and 63 additions
or subtractions**, with 43 positive unknowns and 31 equations.

The predecessor is the complete 121-operation component in
`EXPLORATION_IMPLICIT_BOUND_SERIAL_COMPOSITION.md`. Its raw input, three
registers, signs, source-zero tests, fixed labelled graph, and all-zero
final bank are preserved. This is an operation reduction for that complete
composition, not a new universal-machine compiler or an improvement to
the universal 90-operation frontier.

The full source schedule and receipt are
`../verification/explore_merged_serial_bounds.py/.json`.

## 1. Replace the two positive bounds by one

Use J=(q-1)/2 and the predecessor's raw program words C,V and Test words
TC,TV. Its fixed constants satisfy Zall>S. Indeed the flag target terms
in Zall have positions strictly higher than every state position in S.
Its support equations give the exact identity

    TC+TV=J+C+V+(Zall-S)H.                       (1)

Replace the two equations

    2T+alphaT=q,
    TC+TV+alphaP=q

by a single equation with one positive supplied slack beta:

    T+TC+TV+beta=q.                              (2)

Before any mask or digit interpretation, C,V,H are positive and (1)
gives TC+TV>J. Equation (2) therefore implies T<=J, and also TC+TV<q.
In particular the old slacks

    alphaT=q-2T, alphaP=q-TC-TV                  (3)

are positive integers. This deduction does not assume a raw zero flag
FZ-J is nonnegative. It gives exactly the old paid preliminary bounds,
so every range, native-field, zero-test and controller argument of the
121-operation predecessor remains available in its original order.

The change is stronger than merely deleting a bound. A malformed positive
tuple satisfying (2) cannot evade either old bound: (1)--(3) restore both
of them arithmetically before the kernel is used.

## 2. A larger fixed frame threshold supplies the converse slack

For the constant program table put M=KS+Zall. Choose the new fixed power
of three Rmin at least as large as the old threshold and satisfying

    Rmin>12(M+1).                                (4)

Retain the one charged multiplication R=Rmin*zR. Changing this fixed
coefficient costs no operation. Taking Rmin to be a power of nine, as
in the checker, preserves all predecessor divisibility conveniences.

Take an actual admissible serial history ending with all counters zero.
Its last source counter value is one, and its final sign is minus: a
nonnegative integer can become zero in one +/-1 step only that way.
Consequently its last source-zero label is zero. In the common mask

    T=(R/3)H+((R-3)/6)Z,

the highest R-block is therefore R/3. Every earlier block is at most
(R-1)/2. Writing q=R^u gives the exact upper bound

    T <= q/3+q/(2R)-1/2.                         (5)

The canonical program support word has C<=SH, so TC<=J. The canonical
junk satisfies V<KSH: at least the selected next-state output is
positive and removed from KC. Hence

    TV<MH, H=(q-1)/(R-1).                        (6)

Combining (4)--(6), with R>=9, gives

    T+TC+TV
      < q[1/3+1/(2R)+1/2+M/(R-1)]-1
      < (35/36)q-1 < q.                         (7)

Thus beta=q-T-TC-TV is a positive integer. All native flags, zero
guards, router equations, packing and fixed-sign kernel hypotheses are
unchanged. Choose R divisible by the new Rmin and sufficiently large
for the finite counter values, and use the predecessor's full canonical
construction. It supplies every new positive witness.

This is equivalence of the labelled-history relation. It is not a claim
that every old witness at its old width satisfies (2). An old accepting
history may be re-encoded at a larger R. Conversely, a new witness restores
the two old slacks by (3), and its old threshold quotient is obtained by
multiplying zR by the fixed positive integer new_Rmin/old_Rmin. Therefore
the input and the actual finite labelled path are preserved in both
directions, even when the particular width and packed integer change.

The last-zero-label condition in (5) is a consequence of this component's
zero endpoint. Applying this merged bound to a component with arbitrary
nonzero final registers would need a new converse argument.

## 3. Exact arithmetic changes

The old two bounds use four additions:

    twice_T=T+T, top_bound=twice_T+alphaT,
    program_sum=TC+TV, program_bound=program_sum+alphaP.

The new single bound uses three:

    program_sum=TC+TV,
    combined_sum=program_sum+T,
    program_bound=combined_sum+beta.

The old top-mask calculation was 3*twice_T. Replace that product by
6*T; otherwise twice_T would remain live and there would be no saving.
The product count is unchanged. This replacement is the identity
3(T+T)=6T, with the fixed numeral six free.

Independently, program_C_lhs=C+J is already computed for source support.
The separate program_native_C=J+C instruction duplicates it. Delete that
addition and compare the supplied native NC directly with program_C_lhs.
Its source polynomial is exactly unchanged.

Thus the complete 121-operation schedule loses two additions, giving
119=56M+63A. Two positive slacks are replaced by one, giving 43 unknowns;
two equations are replaced by one, giving 31 equations. Apart from the
merged bound and the stronger fixed threshold, every source polynomial
is identical to the predecessor. The acyclic Pell norm correction retains
its prior index because the removed top-bound comparison occurs after
the kernel comparisons.

## 4. Evidence and limitations

The checker verifies all 119 primitives and all 31 source comparisons,
including the duplicate-adapter reuse, the new top-mask product, the exact
merged equation, the fixed threshold change and the retained norm
correction. A small exhaustive positive-tuple regression checks that the
merged bound restores both old slacks without digit assumptions.
Independent scalar tests check the final-block estimate and the strict
margin in (7).

The receipt records 119,754 positive merged-bound tuples, 600 strict frame
margin cases, and all 765 tested short zero-head sets whose final bit is
zero. None of the old bounds is used as an acceptance filter in these
merged-bound checks.

Two complete canonical labelled paths, with x=1 and x=2, are re-encoded
at the stronger fixed threshold. They check all outer source residuals,
the new positive slack, all twelve native fields, the first unit digit,
the even packed index, exact central-binomial valuation and the full
positive-kernel hypotheses. The enormous Pell witnesses follow from the
predecessor's general positive converse and are not numerically built.
The two examples have 12 and 18 serial blocks, packed words of 333,222 and
499,833 bits, and exact valuations 210,240 and 315,360 respectively. Each
checks all 21 new outer residuals and all 22 restored predecessor outer
residuals. The newly compiled frame width is 1,460 ternary digits.

No bound has been removed merely on the strength of finite examples.
The source identity (1) excludes weakened-bound aliases, and the last
source block plus paid fixed threshold proves the positive converse.
