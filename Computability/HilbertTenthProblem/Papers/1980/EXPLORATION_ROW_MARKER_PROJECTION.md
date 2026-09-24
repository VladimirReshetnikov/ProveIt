# Carry intervals project row markers to selector bits

This is a conditional arithmetic component for a different history encoding,
not a new universal certificate. It can both certify that a row has at most
one marker and recover its presence bit. The component is relevant to the
variable-length morphism in the tag-system proposal. Its radix geometry,
Boolean masks, ranges, and strictly positive witness adaptations remain
paid obligations. The established universal bound remains 90.

## 1. Exact rowwise equivalence

The single-row carry interval `2Q+1=3^p` also appears in
`EXPLORATION_TERNARY_COUNTER_CONTROL.md`. The result here extends it
to independently optional markers in many rows, with the head and
boundary conditions needed to prevent associations across rows.

Let `R=3^m`, with `m>=1`, and let there be `t>=1` rows. Put

    H = 1+R+...+R^(t-1),   A = R/3.

A Boolean word here has only zero and one as ternary digits. Suppose
`Q,M,Qtop,S,Sbar` are nonnegative Boolean words below `R^t`, and impose

    S+Sbar = H,
    Qtop = Q+A*H,
    2Q+S = M.                                           (P)

Then every row `j` is exactly one of the following:

    absent:   S_j=0,  Q_j=0,             M_j=0;
    present:  S_j=1,  Q_j=(3^p-1)/2,     M_j=3^p,
                                                   for some 0<=p<m.

Conversely, any choices of absent rows and present marker positions give
exactly one tuple satisfying (P), with `Sbar=H-S` and `Qtop=Q+A*H`.
In particular, no separate one-marker premise for `M` is required.

The first equality has ternary coefficients at most two, so it forces
`S,Sbar` to partition the row-head mask. The second equality likewise has
no carries and forces the top digit of every `Q` row to be zero. Hence

    0 <= 2Q_j+S_j <= A < R.

The last equality therefore holds separately in every row. If `S_j=0`,
the lowest nonzero digit of `Q_j`, if any, would give a digit two in
`M_j`, which is impossible. If `S_j=1`, let `p` be the first zero digit
of `Q_j`; the top-zero condition guarantees one exists. The initial run
of ones carries to give `2Q_j+1=3^p` below and at position `p`. Any
further nonzero digit of `Q_j` would again give a digit two, so there
are none. This proves the asserted unique form and its converse.

## 2. What the boundary guard and head mask prevent

The top guard cannot simply be dropped. With two rows of radix nine,

    Q=4, S=1, Sbar=9, M=9

are Boolean and satisfy the other two equations. The selector in the
first row is incorrectly paired with a marker in the second. Its carry
crosses the row boundary. The proposed `Qtop=34` has a digit two and is
rejected.

Nor may one keep only `Qtop` Boolean and omit the mask on `Q`. At the
same geometry, `Q=6,S=1,Sbar=9,M=13,Qtop=36` satisfies all displayed
equalities and all other Boolean conditions. Its first `M` row has two
markers. Here `Q` has a digit two.

Typing the selector is also necessary: the scalar equation admits
`R=9,Q=0,S=M=3`, which puts a selector away from the row head.

## 3. Exact conditional operation count

If `R,H` and their asserted geometry are already available, supplying
`A` with `3A=R` gives this six-operation schedule:

    threeA=3*A; top=A*H; Qtop=Q+top;
    headsum=S+Sbar; twiceQ=2*Q; projected=twiceQ+S.

The three free comparisons are `threeA=R`, `headsum=H`, and
`projected=M`; `Qtop` is one of the words sent to the Boolean predicate.
There are three multiplications and three additions. If `A` is already
available from the surrounding geometry, the incremental count is five.
The five Boolean words, their packed bounds, and the geometry are not
included in these component counts. In particular the existence of the
quotient `A` is not silently treated as a free division.

All-zero auxiliary words are possible. For example a marker at every row
head makes `Q=0`. This lemma is stated over nonnegative integers; it does
not silently supply a system with strictly positive unknowns. A positive
adapter or an appropriate forced non-head marker must be counted when
composing it with the current kernel.

## 4. Possible use in a morphism or tag transition

The integer `M` can mark the start or length of an appendant in each
row, while `S` records exactly which rows contain it. Consequently (P)
provides a paid way to project variable marker positions to a regular
selector stream. It does not merely compare the total number of markers.

If a row already has a length marker `L_j=3^ell_j`, a subset marker
`M_j` selected by this relation equals `S_j*L_j` once a Boolean
partition `M+Mbar=L` is also imposed. For the binary tag productions
`0 -> 0` and `1 -> u`, with deletion number `beta`, appendant length
`a`, and ternary little-endian value `U`, the scalar step equations are

    3^beta Nnext = N-d+U*M_j,
    3^beta Lnext = 3L_j+(3^a-3)*M_j.

All coefficients in these two equations are fixed numerals. Thus the
nonlinear selection of the variable length marker can be replaced by
the carry-interval component before packing whole histories. This is
only a proposed interface: deleted-prefix typing, alignment, adequate
row padding, initial input, halting, masks and positive witnesses must
all be included before a universal count can be stated. The separate
eventual-halting stream theorem removes causal-prefix guards, but does
not establish those missing arithmetic interfaces.

`../verification/explore_row_marker_projection.py/.json` checks the
displayed DAG, exhaustive small one-row and multiple-row instances, all
converse marker choices in its stated ranges, and the three omission
examples above. The general proof is the carry argument in Section 1.

## 5. A guard at any fixed depth gives extra row padding at the same cost

The top position is not essential. Let `0<=b<m`, set `A=3^b`, and
retain exactly (P), including the Boolean masks on Q and Qtop. Then
the present-row conclusion strengthens to `M_j=3^p` with `0<=p<=b`.
Thus every row marker is at most A, while absent rows still have
Q_j=M_j=0. Every such choice has the same unique converse.

Indeed Qtop=Q+A*H has raw coefficients at most two, so it forces the
digit at position b of every Q row to be zero. Before using the last
equation, this already gives

    Q_j <= (R-1)/2-A,
    0 <= 2Q_j+S_j <= R-2A < R.

There is no row carry. The first zero in a present Q row occurs at or
before b; the same carry argument as in Section 1 excludes any later
nonzero Q digit. Conversely the interval ending at any p<=b clears
the guarded digit, so all five masks hold.

In particular fix any numeral `C=3^k`, with k>=1, and replace `3A=R`
in the schedule by `C*A=R`. Positive integral A and the known radix
R=3^m imply m>=k and A=3^(m-k). This remains **six operations, 3M+3A**,
with the same five fields, but now enforces `M_j<=R/C`. The quotient
equation is paid; neither a variable exponent nor a free division is
introduced. Setting S=H gives a length marker in every row and makes
the zero selector complement unnecessary when composing that special
case; no whole-system saving is inferred from that observation.

This matters for tag histories. Fixed coefficients such as the deletion
factor and appendant value may be large. Choosing the free fixed C
large enough can keep all rowwise transition expressions below R.
The previous guard is the special case C=3; arbitrary fixed padding
does not require another mask field or another arithmetic operation.

The checker additionally enumerates every guard position for widths
one through four and one or two rows, checks exactly all allowed
marker choices and their converses, and evaluates the modified six-step
DAG for every such choice. These remain conditional nonnegative
components; the full tag input, packed mask and positive-domain
composition are not supplied by this lemma.
