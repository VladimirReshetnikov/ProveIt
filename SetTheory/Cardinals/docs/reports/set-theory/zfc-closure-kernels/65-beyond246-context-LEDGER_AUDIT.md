# Independent review of the two-action search ledger

The inspected final record has 46 state entries, 5,196,550 recursive nodes,
5,216,260 literal fixture checks, 44,539,776 pruned complete assignments and
zero survivors. Summing the per-state `planned`, `pruned`, `nodes` and `checks`
fields independently reproduces every reported total. For each state,
`planned = pruned + survivors = 968256`.

## Domain count

The baseline has 246 working states and one separate halt label. Removing one
working state leaves 245 working targets and the halt target: 246 choices.
Each incoming row can independently choose two writes, two movements and 246
targets, for `2*2*246 = 984` actions. The two external incoming rows are distinct,
so their Cartesian product has `984*984 = 968256` assignments. Across 46 deleted
states, the declared family has `46*968256 = 44539776` recipes.

The generator obtains the 42 protected state/read pairs directly from the
literal and unary-induction traces in the frozen macro certificates. Both
their source states and their successor states are protected, along with
dispatcher 96 and blank-start interface 95. A deleted state's two external
incoming rows must also lie outside this support. Thus the original local
register-operation proofs are unchanged throughout this declared family.

## Why the lazy partition does not omit a bounded case

At every recursive node, assigned incoming actions are fixed and all other
machine rows are fixed. The executor stops before executing any unassigned
incoming row. A hole encounter therefore identifies an action that can affect
this finite trace; the recursion branches over all 984 choices and restarts
the original fixture for each branch.

If a trace fails before another unassigned action is queried, its behavior
through the declared bound is independent of that unassigned action. The
rejected node therefore covers `984^u` complete assignments, where `u` is its
number of unassigned rows. This includes finite-fuel failures: their conclusion
is explicitly about the bounded screen, not eventual execution.

Every branching step partitions the node's completions into disjoint children
by the chosen action. Every failed leaf records exactly the size of its
remaining completion set. Any completely accepted assignment would be counted
once as a survivor. Moving a failing fixture to the front changes only test
order; every recursive child restarts from the original fixture and action
assignment. The recorded mass identity is therefore the expected coverage
invariant of the implemented recursion.

## Why originally unaffected fixtures need no mutation-dependent selection

The altered table differs only at the two incoming rows and the removed state's
rows. If an original literal fixture never visits any of those rows, induction
on its original finite execution shows that the altered table takes exactly
the same transitions until the same endpoint. All possibly affected fixtures
are selected from the baseline's complete literal transition footprints.

This footprint argument is used only for finite screening. Every reported
survivor would additionally be replayed against all 8,391 fixtures with a
20,000-step bound. No such survivor exists in the final record.

## Bounds and interpretation

The affected-case gate permits 2,000 literal transitions. The separately
validated reference takes at most 558 transitions on these fixtures. Tape
coordinates are limited to -64 through 447. Exact repeated-configuration
detection compares the complete represented tape, state and head directly;
it introduces no hash-collision assumption. The fixtures use specified finite
register values and spare suffix `[0,2]`.

Accordingly, the completion result is an exhaustive partition of this bounded
44,539,776-recipe screen. It is not a proof that those machines never reach the
expected endpoints after the bound, nor a state lower bound, nor a proof that
all alternate semantics are impossible. The source and fixtures make the
record reproducible without trusting the saved arithmetic totals alone.
