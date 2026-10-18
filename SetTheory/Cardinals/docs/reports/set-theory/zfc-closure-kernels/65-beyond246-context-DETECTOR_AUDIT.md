# Independent audit of the bounded detector synthesis

This reviews the root investigator's `synthesize_detector.py`. It does not
claim a successful eight-state detector. The reported nine-state SAT result
is a positive control; the eight-state bounded UNSAT and UNKNOWN results have
the limitations below.

## Interface and exhaustive finite input partition

Synthesized state 0 represents old state 4; synthesized state 1 represents old
state 6; synthesized exit label `n` represents old state 84. The fixed rows
`0/0 = (0,L,1)`, `0/1 = (1,L,0)` and `1/1 = (1,L,0)` are exactly the three rows
used by the retained marking contracts.

Every incoming edge to old state 4 writes one and moves left. Therefore,
whenever that state is entered in the inherited machine, the cell immediately
to its right is one. This is a direct control-table invariant, independent of
the source program's PC values or any finite blank execution.

The ten synthesis fixtures cover a first one after 0 through 8 leftward zeros,
or nine initial zeros. The known right-neighbor one is also represented. For
the first nine fixtures, the desired endpoint is state 0 immediately to the
left of the discovered one. For nine zeros, the desired endpoint is the exit
label immediately to the left of the ninth zero. In every case, the full known
tape window must be restored exactly.

Active-head bounds prevent the synthesized machine from reading to the left
of the discovered one, to the left of the ninth zero in the final case, or to
the right of the known right-neighbor one. Although unspecified exterior bits
are encoded as zeros in the solver's finite tape word, those bits cannot be
read or written during an active trace. A SAT table whose ten traces replay
literally therefore has the stated local contract for arbitrary exterior
contexts, by a finite partition on the first nine bits.

## Bit-vector semantics

The active state is constrained below `n`; successor labels are constrained
at most `n`. The head is bounded before each active transition, so the
five-bit arithmetic cannot wrap on a legal trace. The shifted write mask and
eleven-bit tape word have matching widths. The row-selection conditional
chooses the corresponding state/read row for every active state. Finished
configurations are absorbed, making a shorter execution satisfy a larger
step bound without inventing further transitions.

## Symmetry restriction

The clause requiring every working state `q > 0` to have an incoming edge
from some smaller-index state is a valid breadth-first naming convention
provided all `n` working states are reachable in the finite control graph.
State 1 remains fixed under such renumbering: state 0's two successors are
already fixed to 1 and 0, so state 1 is necessarily the first new state in a
breadth-first traversal.

The clause also requires all `n` states to be graph-reachable. Consequently,
an UNSAT result should be described as applying to the stated exact-size,
reachable-state template and the stated time/window bounds. It must not
silently become a proof that no machine with *at most* `n` states exists.
Separate smaller-state runs or a justified padding argument would be needed
for that stronger interpretation. None of the bounded UNSAT results is a
global state lower bound.

## SAT export detail

A future SAT model may leave an unvisited transition's write or direction
unassigned. Export should call `model.eval(variable, model_completion=True)`
for all transition variables before converting them to integers/Booleans.
This supplies arbitrary legal values for unused model variables and avoids
an export exception. Literal replay of every returned SAT trace and a final
check of all fixed interface rows should remain independent validation steps.

UNKNOWN, including timeout, carries no unsatisfiability conclusion.
