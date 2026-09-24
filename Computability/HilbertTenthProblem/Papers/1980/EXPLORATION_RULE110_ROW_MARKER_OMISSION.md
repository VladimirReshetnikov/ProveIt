# A full false history when the Rule 110 row marker is removed

This note concerns one specific proposed deletion from the
[zero-offset history75](EXPLORATION_ZERO_OFFSET_RULE110_HISTORY.md).
Replace the low packed field `T=bC+H` by `C`, keeping every other
equation, including the width divisor and the repunit geometry. The
product `bC` and addition of `H` disappear. The resulting source has
**73 operations, 42M+31A**, 25 positive unknowns and 16 comparisons.
It is not a valid certificate of the intended finite-history relation.

## 1. The exact changed source

Use radix b=128, with the other definitions of history75:

    W=bA, q=W*quot, q-1=H(W-1), I+alphaI=A,
    I+WY=C+qF, (b-1)J=q-1,
    U=(18b^2+23b+23)C+42Y,
    L=q^3, D0=q^5,
    P=C+qY+q^2 U,
    M=J[(b-2)(q+1)+36q^2],
    r=(L-P)(L-1)+M.

Retain all ten fixed-minus kernel equations without alteration. Thus
the change affects the actual packed index and its fresh Pell witnesses;
the example below is not just a local counterexample to a digit rule.

## 2. Exact positive outer witnesses

For a nonnegative integer z, let E_b(z) replace its binary digits by
the same zero/one digits in radix b. Set

    m=3, t=9, N=mt=27,
    I=1, F=b,
    C=E_b(32917465), Y=E_b(37669115),
    W=b^3, q=b^27, A=b^2,
    quot=b^24, H=(q-1)/(W-1), J=(q-1)/(b-1),
    alphaI=b^2-1.

All supplied outer coordinates are strictly positive. Direct exact
integer arithmetic verifies

    I+WY=C+qF,
    b^2 C<q, Y<q,
    Y=Rule110(bC)

where the last equality applies Rule 110 once to the entire concatenated
zero-exterior word. In binary cell notation, the last identity is

    37669115 = ((32917465<<1) OR 32917465)
               AND NOT ((32917465<<2) AND
                        (32917465<<1) AND 32917465).

Consequently the zero-offset scalar rule is correct at every digit of
the concatenation. Every actual digit of U is between0 and106 and has
zero intersection with36. All three fields C,Y,U are below q, and

    P AND M=0, 0<P<L, 0<M<L.

The packing therefore gives a positive integer r with

    q^3-1<r<q^6,
    popcount(r)=5*7*N=945.

Since C is odd, P is odd. M is even and L is even, so r is odd. The
complete positive converse of the fixed-minus43 kernel at scale q^5
therefore supplies its remaining sixteen auxiliary coordinates. All
ten kernel equations hold. As in the valid history75 proof, the huge
Pell coordinates are constructed by the general converse rather than
materialized in the finite checker. The source tuple is thus a complete
positive false solution, with every retained comparison accounted for.

## 3. Why the claimed endpoint is impossible

In a genuine moving Rule 110 step, a nonempty word's least occupied
position is unchanged. If that position is j, the local triple at the
corresponding output position is `(0,0,1)`, which outputs1; every lower
triple is zero. Starting from I=1, every genuine positive-time endpoint
therefore has its least occupied position0. The proposed endpoint F=b
has its least occupied position1, so no genuine finite history connects
these parameters at any time.

The removed marker prevented information at the end of one stored row
from entering the beginning of another. Checking the local rule on a
single concatenated word does not provide those separate row boundaries.
Indeed `bC+H` is not Boolean in this example; the original75 source
rejects precisely the omitted constraint.

## 4. Scope and verification

[The checker](../verification/explore_rule110_row_marker_omission.py)
compares all sixteen changed source residuals with the complete73
schedule, constructs the positive outer tuple, verifies every outer
equation and mask, checks the exact valuation and odd parity, and
rejects the tuple in the original marker field. It also checks the
same digit construction at radices256 and512. This refutes the stated
two-operation deletion, not all possible73-operation encodings.

Review status: author and independent complete scoped proof/source review
pass. The independent fresh run matches the saved receipt exactly, with
the proof, source and receipt hashes unchanged. It verifies the full
changed source and all three actual indices and positive extensions.
