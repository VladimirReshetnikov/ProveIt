# Independent review: actual step construction and trace bounds

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Result: **PASS**;
no correction requested to either frozen packet.

Circuit authored both target modules and their checks. The reviewer did
not author or edit them. The reviewer authored the separate converse
`WangTiles942RowStep` proof, along with earlier arithmetic/window and
strip/reset modules. That related work uses the same Action, Step and
finite-language interfaces, but none of those reviewer-authored modules
is an input to these two packets. Complemented authored MachineAction,
MachineStep and MachineEncoding; the exact decoder/table and operational
Core dependencies are existing work. This is an independent review of
the two new packets, not independent authorship or a fresh replay of the
entire dependency closure.

All Lean paths below are relative to `Lean/DiophantineConsistency/`, except
the explicitly named repository Core path.

| Reviewed source | Lines | SHA256 |
| --- | --- | --- |
| `WangTiles942StepConstruction.lean` | 159 | `935bfb4b2762bd099185350f3869114c81f11140a823951e6319a33ce292138f` |
| `WangTiles942StepConstructionChecks.lean` | 114 | `5e8c6382fceabcf880ca431af455cb71d90350b107c10f5c748eb3a4dd688a92` |
| `WangMachineTraceBounds.lean` | 142 | `2a4c16552c74a33445f8aa5302d5ab108f327708a08f468c4e61e6afcd85e718` |
| `WangMachineTraceBoundsChecks.lean` | 85 | `22e106989ecf6d9958fc6b86c650797d489b4b2734ca076391c8b2dedcae944c` |
| `WangMachineAction.lean` | — | `1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5` |
| `WangMachineStep.lean` | — | `479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100` |
| Repository `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean` | 808 | `436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6` |

I read every line of both target modules, both checks and both author
receipts before execution. I also read the complete Action, Step,
MachineEncoding and Core sources, checking the exact input index,
write-before-move semantics, halted-state convention, read/write lemma
and run/runFrom equations used here. The target source hashes match their
author receipts and stayed unchanged through replay.

The step constructor is an actual row, not an assumed calibration. Its
old-head branch uses the literal transition indexed by the actual state
and read bit; its moved-head branch uses the corresponding directional
receive tile with the old destination bit; every other position receives
the plain pass tuple. The actual move changes the head by exactly one,
so the first two branches cannot overlap. Membership in `Allowed` is
proved from the exact transition/receive/pass constructors. No unproved
table inclusion is supplied as a premise.

The north-color interpretation requires precisely `cfg.state=some q`.
The south-color interpretation matches the complete actual operational
step. It retains an action whose next state is `none`: the write and move
still occur and the receiving head gets432 or433, determined by the old
destination bit. The target is not silently restricted below215. The
west/east formulas identify the single signal edge for either direction;
the horizontal proof uses `x+1=newHead ↔ x=oldHead` for a right move and
the corresponding reversed identity for a left move. Thus the direction
agrees with the marked-plane convention.

The public `step_row cfg q hq` constructs allowed tiles with exact north,
south and horizontal matching at every integer position. It assumes no
tape normalization, already constructed row, native calibration, finite
rectangle, run encoding or target-not-halt condition. The concrete checks
include the actual first action, actual left action5 and halting action125
on a duplicate-containing tape, with destination bit1. The checks obtain
actual `Fin 942` tile witnesses from the existing `Allowed` equivalence.

The trace bounds are independently generic in the state count and machine.
The step-head proof treats halted configurations as stationary and live
actions as one left/right move, regardless of the next state. Away from
the old head, the tape read remains unchanged. This latter fact uses read
semantics of the actual finite-list tape; no `Nodup` or support assumption
is hidden in the interface.

The inclusive tape endpoint is correct. After `t+1` steps, a position at
or beyond `initialHead±(t+1)` differs from the head at time `t`, whose
position lies in the closed earlier interval. The final write therefore
cannot touch that endpoint. Induction transfers its read back to the
initial tape. For a blank run this proves `|x|≥t → read=false`, including
the entire tape at `t=0`; it does not incorrectly claim that the head
lies in the corresponding open interval. The head bound is closed,
`−t≤head≤t`, and both extremes are exercised by the one-step checks.

`finite_trace_box` uses independent margins `T<L` and `T<R`, so all heads
through timeT are strictly interior and every position on or beyond
either wall is blank. This supports unequal margins and makes no
divisibility or halting assumption. `halted_trace_box` extends the same
box to every later time only under the explicit hypothesis that the
actual run is halted atT, using stationary halted execution. Zero-state
machines, initially unnormalized/nonblank tapes, entering halt and the
impossibility of uniformly tightening the tape threshold to`t−1` are
covered by the focused checks.

Independent fresh replay used a new temporary object namespace at
`/tmp/wang-step-trace-controller-peer`. It symlinked only existing
prerequisites and excluded every entry belonging to all four reviewed
module/check stems. Each main and check was freshly compiled sequentially
with an explicit first-priority `LEAN_PATH` overlay and `-M6000 -j1`.
The checks imported the new main objects. No shared prerequisite object
or source was modified.

The command pattern, applied separately to the four reviewed stems, was:

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/wang-step-trace-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 SOURCE.lean -o /tmp/wang-step-trace-controller-peer/DiophantineConsistency/STEM.olean'
```

All four commands exited zero. Both main logs contain only the timing
record, with no Lean diagnostics. The two checks emitted thirteen intended
axiom reports each; all 26 sets are subsets of `propext`, `Classical.choice`
and `Quot.sound`. No `sorryAx`, custom axiom or native-decision axiom occurs.

| Replay | Seconds | Peak KiB | Timed log SHA256 |
| --- | ---: | ---: | --- |
| Step main | 4.15 | 3200656 | `ba4f4e2f9dc29336297c129dd93c42b4f7c63bf8f5ae2916678e98a938671773` |
| Step checks | 4.15 | 3193224 | `8f39aa6cec03786af5f077d8558313fa150537938c30fd9f281ef4554b340cb4` |
| Trace main | 2.53 | 1494736 | `95379893e868997de4e4d36ed5b7b7e057ce70facc03b4e9f34e4f7af37b38f3` |
| Trace checks | 2.47 | 1492108 | `4b3bc0d874dabdbb0856a137f223a892c53c2414762b5370bf656995219a64bd` |

The fresh main objects are byte-identical to their original frozen
objects: StepConstruction
`3f45c3b95da12326c9b15fd930f2993fdb3cb722f1fbe90822273f2ecf987049`
and TraceBounds
`7314d6ac41954c4276bab11a207b741e01b3745af4c2bcfe50496a5822bc6350`.
The original checks had no saved shared objects; the independent fresh
objects are respectively
`038dbedc70c7b5ea92ad5735731d9da5978d97272746589216e9f1569a8d4cba`
and `e0df6ce24d3c4b824950fcd159c1dba87fb3eacaa8cda28b94eedac5bde7665a`.
The input manifest SHA256 is
`7257ccd2920315dbe08100a39c69cb4ef820201feee04697d96f1700e62324bf`;
all15 recorded source/object/toolchain inputs were rehashed unchanged.
This is a target-packet replay against existing dependencies, not a fresh
compilation of their full closure.

Scope remains precise: the packets construct one operating step and
bound actual finite traces. They do not yet construct a complete periodic
Wang rectangle, prove cofinal admissible rectangle sizes, construct the
reverse arithmetic witnesses or establish the final consistency
equivalence. No such stronger theorem is inferred by this review.
