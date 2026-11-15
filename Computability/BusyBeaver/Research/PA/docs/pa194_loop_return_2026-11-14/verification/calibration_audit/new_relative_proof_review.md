# Review of the new relative proof

Reviewed: `report/relative_proof.tex`, `build.py`, `construction/support.py`, and the recorded shortcut premises in the `pa194_loop_return_2026-11-14` package. The mathematical review found no correction necessary. The following are the critical points checked, not a claim to have performed a separate proof-assistant build.

## The three shortcuts

The proof's four incoming-bit implications are a closed quantifier-free invariant for runs from native control 74. For control 26 reading one, its incoming edge from 101 is impossible because the unique incoming edge to 101 has just written zero immediately to its left. Its incoming edge from 11 writes zero at the new right neighbor. Since the new current bit is one, the old left neighbor of 11 is one; the disjunctive invariant at 11 therefore forces the old right neighbor to be zero. That is precisely the new second-right neighbor needed for the three-step block.

For control 190 the unique incoming edge is the new loop-parent row `139/1 -> 1R190`, so the left neighbor is one. The replacement `190/1 -> 0L42` agrees with the three-step route through 73 and 83 on the whole tape and head. The two other shortcuts have the same exact three-to-one property under their respective guards. None of the skipped controls is the halt label. The stored twenty five-cell cases cover every combination consistent with the guards; the written locality argument makes exterior cells irrelevant.

The expanded clock is primitive recursive: at each accelerated step its increment is three for a changed row and one otherwise. With an absorbing halt, including increment one after halt, quantifier-free induction proves exact configuration equality at the expanded clock and the bounds `t <= sigma(t) <= 3t`. Thus a parent halt by `t` implies an accelerated halt by `t`; an accelerated halt by `t` implies a parent halt by `3t`. No inverse-clock search is needed.

## Connecting the loop reassociation to the old source

The source reassociation changes paths, so equality of resolved primitive instruction arrays is the appropriate source comparison. It identifies all register updates, both decrement edges, jumps, and the halt-ready site by ordinal. The literal physical contracts are a separate obligation and cannot be inferred just from this source equality. The build and independent verification mechanisms preserve that separation.

The ready-to-halt convention is internally consistent: the source frame at the halt instruction still has nonhalting dispatcher control 84, and the halt instruction has its own positive-duration contract. The product `P(j)` of earlier nonhalt indicators allows induction only over normal prefixes. If the physical machine has halted by time `t` but `P(t+1)=1`, the exact future frame at time at least `b+t+1` is nonhalting, contradicting absorption. Since `P` is a finite Boolean product, its failure supplies a first halt-ready source index at most `t` by bounded search and quantifier-free induction. This uses decidability of a bounded finite list, not Markov's principle.

The tape-zipper updates in the report have the correct low-bit orientation for both moves. They preserve the required halting behavior of the complete finite-support tape. Absolute head position can be retained as an extra integer counter if desired; the source contracts separately record zero boundary motion.

## The polynomial bound

The proof requires the coefficient envelope to be checked for all contracts of both new tables and both frozen parents. Conditional on that stated finite audit, the arithmetic calculation is correct:

`1000 + 8(2j) + 4(2+j) + 2 + 2(75+3j) = 1160 + 26j`.

The spare-tail width must be included: every appended spare equals one and therefore adds three cells to that width. The initial twenty-five tail spares have width 75; the first spare remains one. The gap bound `2j` is conservative: the current closure checker actually reports zero address overflow, so only positive decrements increase it in these programs.

Summing through `n` normal instructions and the final halt instruction gives `13(n+1)^2 + 1147(n+1)`. With every startup below 60000, this yields exactly `Theta(t) = 13t^2 + 1173t + 61160`. Extracting the common logical halt index `n <= t`, then applying the other implementation's bound, establishes the two stated relative witness implications inside iPRA.

## Scope of the conclusion

This relative argument is independent of PA consistency and of the inherited arithmetic proof compiler. Composing it with the explicitly retained AX11GH/GHS written calibration yields the absolute written consistency equivalence. The separate `calibration_audit.md` explains which parts of that inherited dependency were examined and which formalization work remains outside this review.
