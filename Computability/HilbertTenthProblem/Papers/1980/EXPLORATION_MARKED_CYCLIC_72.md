# A 72-operation positive certificate for marked finite-table halting instances

For every deterministic Turing machine `M` and finite input word `w`, one
can effectively construct a system with **72=41M+31A**, 27 strictly
positive unknowns, and 17 equations, which has a solution exactly when
`M` halts on `w`. The machine and its input are compiled into the fixed
numerals. No cost is charged for constructing those numerals, as required
by the chosen complexity measure.

This is a uniform effective reduction of halting instances to bounded-size
systems. It is an **encoded-instance** result: its fixed numerals depend
on `w`. It does not assert one fixed set of coefficients for all raw
numerical inputs to a given machine. The established89-operation
raw-input universal certificate therefore remains the universal frontier.

The theorem combines three proved constructions:

* the [marked periodic TM tableau](EXPLORATION_MARKED_PERIODIC_TM_PADDING.md),
  with independent width and height padding;
* its [four-cell lift](EXPLORATION_FOUR_CELL_PERIOD_LIFT.md), preserving
  every period and one fixed accepting marker;
* the [complete70-operation cyclic arithmetic certificate](EXPLORATION_MULTIBIT_CYCLIC_CERTIFICATE.md).

The final acceptance equation has exactly two additional operations.
The [checker](../verification/explore_multibit_cyclic_certificate.py)
and its [receipt](../verification/explore_multibit_cyclic_certificate.json)
record the70 and72 source schedules separately.

## 1. A two-operation marked-occurrence interface

Fix a finite four-cell relation `R4` with a distinguished state `X4`.
Choose the injective nonzero Boolean alphabet coding so that

    Enc(X4)=(1,0,...,0).

Under the multi-bit compiler, this state with all dummy bits zero has
the scalar code2. The other states receive distinct nonzero codes.
Use the complete70 system and add one positive unknown `T` and equation

    C=2+B*T.                                            (1)

The product `B*T` and addition of2 cost one multiplication and one
addition. No other operation changes. Consequently the source count is
72=41M+31A. Its23 existential unknowns, the three former supplied
parameters `q,P,C`, and `T` give27 positive unknowns when all are
existentially quantified. There are17 equations.

Soundness of70 first establishes `C<q` and types its radix-B cells.
Equation (1) then sets its unit cell to exactly2, including zero dummy
bits. Its projected state is `X4`. The decoded cyclic word therefore
contains the required marker. Conversely, a valid cyclic configuration
containing `X4` can be rotated to put it at index zero. Replace every
dummy filling by zero, which preserves all projected local relations.
If necessary, repeat the cyclic word twice to obtain length at least2.
Keep its stride unchanged; repeating a periodic word preserves every
four-cell constraint and the allowed bound `1<=h<=N`.

Every state has a nonzero code, so at length at least2 the quotient
`T=(C-2)/B` is a positive integer. The complete positive converse of70
provides all its other coordinates at this actual modified word. Thus
(1) is equivalent to marked cyclic existence; the positive tail excludes
no possible marked instance. It is not asserted to preserve all original
numerical witnesses at fixed `q,P,C`.

## 2. Exact reduction from a halting instance

For given `M,w`, build the finite alphabet and local3-by-3 relation of
the marked tableau. Its boundary intersection `X` forces an initialized,
finite, closed computation rectangle. The local rules forbid head escape
and require the last computation row to halt. Thus marked totally
periodic existence implies that `M` halts on exactly `w`.

Conversely, if the machine halts, the tableau construction gives marked
tori of every sufficiently large width `W` and height `H`, independently.
The four-cell lift stores vertical triples, is inverse to its middle
projection, and preserves every period. At a boundary intersection,
the neighboring vertical boundary states are both the unique symbol `V`.
The lifted marker is therefore the single state

    X4=(V,X,V).

Choose `h>=2` large enough for width `h+1` and height `h` to meet both
padding thresholds. The coordinate map

    (x mod(h+1),t mod h) -> -hx-(h+1)t mod h(h+1)

is a bijection. The lifted torus gives a valid cyclic word of length
`N=h(h+1)`, with local arguments at offsets `h,0,-h,-h-1`, and a marked
unit cell after a cyclic rotation. Assign zero dummy bits. Then the
positive converse of70 and (1) provide a solution of72.

For the reverse direction, any positive solution of72 decodes to a marked
cyclic word by Section1. Pull it back through

    b(x,t)=state(C_(-hx-(h+1)t mod N)).

It is totally periodic, obeys the four-cell relation, and has a marker:
the index map is surjective, since `(x,t)=(i,-i)` maps to `i`. Its middle
projection is therefore a marked totally periodic original tableau.
The original soundness theorem forces a genuine halt of `M` on `w`.

The soundness direction does not require `N=h(h+1)`. That restriction is
only a convenient completeness choice supplied by independent padding.
Every arrow in this reduction is effective and uses only finite tables.

## 3. What is fixed and what still varies

For each instance `(M,w)`, the construction first chooses a finite
alphabet, its four-cell relation, its nonzero symbol coding, and then all
large arithmetic constants. The final system uses only fixed numerals,
strictly positive unknowns, and polynomial equalities. The72-operation
source evaluates all those equalities, with the same kernel schedule
and acyclic norm correction as70.

Its constants grow with the truth table and can be impractically large.
Their size does not affect this operation count, but it remains part of
the encoded instance. Neither bounded bit length nor a fast numerical
compiler is claimed.

To improve the89-operation raw-input universal theorem, one must instead
fix the machine's alphabet, rule, and arithmetic constants before the
raw integer `x` varies, and implement the connection between `x` and an
initialized accepting tableau inside the counted system. The present
result has paid for geometry, arbitrary finite-state control, all masks,
positive transport, the full Pell kernel, and marked acceptance. It has
not paid for that raw-input connection.

Independent complete scoped mathematical/source review passes for both
halting directions, the marker's whole-cell constraint, positive tail
recovery, and all source counts. The checker verifies all72 primitives
and17 residuals, and independent symbolic recomputation matches the
saved receipt. Six exact marked examples specialize the marker numeral
to2, exercise two length-one repetitions and two nontrivial rotations,
and reject six marker cells with nonzero dummy bits. The underlying
arithmetic and period-lifting evidence is recorded in the linked proofs.
