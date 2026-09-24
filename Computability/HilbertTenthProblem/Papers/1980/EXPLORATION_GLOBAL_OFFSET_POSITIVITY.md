# Positive raw fields under one global native offset

This note proves the positivity interface for replacing twelve separate
native fields by positive raw fields and one global repunit offset. It
does not count the proposed new arithmetic system; that is a separate
full source certificate. The finite checker is
`../verification/explore_global_offset_positivity.py/.json`.

The predecessor is the complete serial three-counter construction,
with ordinary positive input x, physical initial values [2x,0,0], all
three final values zero, and a mandatory first plus instruction. Each
physical update changes exactly its selected counter by +1 or -1 and
all physical values remain nonnegative. Its fixed finite program
compiler is proved in `EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`;
the accepting halt is identified with the prefix entry as justified in
`EXPLORATION_CYCLIC_ENTRY_SERIAL_COMPOSITION.md`.

## 1. A zero request can be mandatory without changing the language

The original fixed prefix consists of the three plus instructions on
registers0,1,2, followed by the three minus instructions on registers0,1,2.
It leaves [2x,0,0] unchanged. Change exactly one source label: the first
plus instruction on register1 now requests that its source counter be
zero. It is the vertex `('prefix','jump',0,1)` in the maintained compiler.

That register still has value zero: the only earlier prefix instruction
updates register0. Thus the new request always holds, for every x>=1.
The six signs, phases, edges and endpoint are unchanged, and the prefix
still restores the initial triple before the computation begins. Every
old valid initial computation remains valid with this label; conversely
removing an extra zero request cannot create a new old computation.
There is no new equation or arithmetic instruction for this finite
control change. Its recompiled ROM numeral includes the new label.

The same assertion holds after an accepting cleanup return. All physical
counters are then zero, so the marked six-step prefix again executes
legally and leaves all of them zero. Before the cyclic quotient, the
prefix entry has no predecessor and the accepting halt has no outgoing
edge. Identifying just these two vertices consequently changes neither
the forced prefix nor the proof that the first positive return comes
from an accepting cleanup. Every positive returning path must execute
the marked vertex before its first return. Later returns do not affect
the acceptance argument for the original x.

The helper `mark_prefix_zero(graph)` copies an ordinary compiler graph
and performs exactly this label change. The helper
`build_marked_graph(code,start)` constructs that marked graph directly.
The existing cyclic-quotient helper can then be applied unchanged.

## 2. Both numerical tracks are strictly positive

Consider any nonnegative unit-step counter walk beginning at 2x>=2 and
ending at zero. It has a source value exactly2. One direct proof takes
the first time its value becomes1: the preceding value must be2, since
the walk starts at least2 and each step changes the value by one.

At every source block the representation decomposes its ordinary
numerical value a as a0+a1, where both a0 and a1 have only ternary digits
0 or1. This sum has no ternary carry: at each position its coefficient
is at most2. If a=2, the unit digits of a0 and a1 must therefore both
be1. In particular both tracks have a positive contribution in that
block, independently of how any other digit1 was allocated between
the tracks. Their complete packed words A0 and A1 are strictly positive.

Apply this argument to the first physical counter, whose updates form
exactly such a walk from2x to0. Interleaving the other two counters only
changes the positive powers of the block radix used as weights; it
cannot remove that positive contribution. This proves track positivity
for every accepted physical history and every valid two-track split,
not only for a specially chosen canonical split.

## 3. The other six raw counter/zero fields

The low eight raw fields, in order, are

    Kplus, A0+T, A0, A1+T, A1, Kminus, Z, D.

All are strictly positive:

- Kplus has the mandatory first plus instruction.
- Kminus has the final instruction. Its source is1 and its sign is
  minus: a positive-length nonnegative unit-step history cannot finish
  at the all-zero triple with a plus instruction.
- Z has the mandatory marked prefix request from Section1.
- D, the complement of Z on the physical block heads, has the final
  instruction. A request that this nonzero source be zero would make
  that instruction inadmissible, so its true zero label is0 and its
  emitted complement is1. The initial prefix instruction also has a
  fixed zero label0, providing another such block.
- A0 and A1 are positive by Section2.
- A0+T and A1+T are positive because T>0. In every positive construction
  T includes the top-place guard in every nonempty source block, whether
  or not a true zero request is present there.

The four remaining raw fields are C,V,TC,TV. They are already positive
supplied variables in the predecessor. Canonically, C contains the
nonempty state path, V has the count-marker unit junk, TC is positive
under the proved program-width bound, and TV includes the nonempty
forbidden mask. Hence all twelve proposed raw fields are positive.

These statements concern decoded valid histories. A soundness proof
for a new source must first establish decoding from its own equations;
positivity of hypothetical decoded tracks cannot be imported before
that stage. For an equivalence proof using native aliases J+raw, the
aliases are automatically positive from the new positive raw domain.
For the converse, the arguments above prove that every needed raw
coordinate satisfies the stronger strict-positive domain.

## 4. The global offset itself

For q=2J+1 and L=q^12, let J12=(L-1)/2. Its defining equation
2J12+1=L has a positive integer solution. The exact polynomial identity

    J12=J(1+q+q^2+...+q^11)

implies that adding J12 to the raw Horner word is exactly the old word
of the twelve native aliases J+raw. This identity has no typing or
carry prerequisite. It is valid before the radix powers are decoded.

In canonical ternary geometry, the global repunit has an even number
of trits and J12 is even. The original even-duration parity argument
for the complete packed index is unchanged by marking the prefix:
Z+D=H still holds, and modifying fixed labels changes neither signs
nor duration. This note does not substitute that observation for the
new system's full kernel and arithmetic proof.

## 5. Evidence scope

The checker exhausts the stated finite unit-walk ranges:1,714 valid
first-plus walks with x=1..4 and length at most14, checked under three
concrete digit-split variants for5,142 split tests. It separately marks
the actual fixed compiler graph, checks prefix preservation on101
inputs including the all-zero restart, and follows every serial edge
and physical update in all31 compiled sample-machine runs. Both
accepting and rejecting runs are retained, while all raw-positivity
assertions are required on each accepting run. It also checks that an
accepting return admits the marked prefix again.

These finite checks support the explicit arbitrary-walk and compiler
proofs above. They neither constitute a complete universal arithmetic
certificate nor numerically instantiate the enormous Pell witnesses.
