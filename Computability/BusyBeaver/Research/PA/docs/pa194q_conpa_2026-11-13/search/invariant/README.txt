PA194Q: inductive source invariant and additional reduction searches
=================================================================

RESULT
------
No machine below 194 states was obtained. This addendum concerns the same
PA194Q action graph as the principal deliverable: its canonical dense-table
SHA-256 is 48e98b5504dc5b3f20a2d040cb54ed1c96bee4c5e32ea27ae98ffada4dce7ea1.
Native labels differ from dense labels; the start is 74 and halt is 254.
The explicit native table is a valid input to the searches, not a rejected
193-state candidate.

THE NEW FINITE INVARIANT
------------------------
abstract_source.py computes an inductive invariant and separately checks its closure
for the nine-register source program. Each register is classified using
unions of {0}, {1}, and {n : n >= 2}, encoded by bits 1, 2, and 4. Increment,
positive decrement, zero decrement, and jumps have explicitly checked
finite transfer functions. Every successor abstract state is included in
the invariant at the target program counter.

The invariant starts at source site 25 with logical values (2,0,...,0).
verify_inputs.py binds the source paths to all 3,649 literal instructions,
recomputes the invariant, checks the canonical machine hash, and executes
57,922 literal blank-tape transitions. It checks the COMPLETE resulting
tape, including the source-address header, all nine primary registers,
26 spare registers, the head location and the control state.

Exactly 3,648 source sites are abstractly reachable. At site 7, the tested
scratch register r6 is identically zero; the positive successor site 8 is
unreachable. Therefore only 4,747 of the original 4,749 primitive outcomes
are needed for source simulation from this verified entry. At the top-level
comparison entry, r6 is restricted to {0,1}.

This is a finite inductive source invariant, not a proof that the machine
never halts. It does not establish the Con(PA) calibration by itself. Its
induction argument is arithmetizable in PA. No new Lean/Rocq theorem is
claimed. The invariant starts AFTER bootstrap and does not justify
unconditional changes to the earlier bootstrap computation.

INVARIANT-SPECIALIZED LITERAL-TAPE REPLAY
----------------------------------------
collect_affine.py specializes all nine symbolic register values to these
facts: a known zero or one becomes a constant, a lower bound 1 or 2 becomes
an affine natural variable plus that constant, and a {0,1} fact is split.
The non-convex set {0} union {n>=2} is conservatively enlarged to all natural
numbers. Impossible source outcomes are omitted. The direct symbolic tape
executor derives its generic list lemmas from the literal transition rows,
checks whole-tape endpoints, and requires positive physical progress.

This replay checked 4,749 affine cases: the 4,747 admissible source outcomes
plus two additional zero/one cases. It observed 22,146 symbolic local views
and produced 29,396 conservative radius-five windows covering all 194
working controls. Unary-loop interiors, generic list-block traces, and
EVERY literal blank-bootstrap configuration are included. The checked
source/path and initial-tape binding is essential to the coverage claim.

Reproduce the input checks:

    python3 verify_inputs.py

Recompute the literal-tape windows (roughly a few minutes):

    python3 collect_affine.py

The original output is retained in contexts_C_affine/. collect_affine.py
writes its fresh output there. Assertions must remain enabled.

EXHAUSTIVE ENUMERATION WITHIN EXPLICIT LOCAL RESTRICTIONS
--------------------------------------------------------
The following searches found no accepted contraction on the frozen affine
window set. They enumerate their stated finite action spaces; their empty
outputs are NOT lower bounds on the number of states of a PA machine.
Conservative windows can include unreachable contexts, and the restrictions
exclude many possible implementations.

1. action_merge_all.cpp searches pairs of non-start controls for common
   replacement first actions. Bounded existing-table continuations must
   reproduce each old one-step endpoint exactly. Its restrictions prevent
   interference through the other member of the identified pair.
2. bypass_all.cpp deletes a non-start state with no self-incoming edge by
   replacing EVERY incoming transition separately. Each replacement must
   reproduce the original predecessor-step plus deleted-state-step effect.
   Different predecessors may use different replacement actions.
3. bypass_join.cpp generalizes (2): the replacement may rejoin the old run
   after between 2 and 24 original transitions. An old segment stops before
   another modified incoming row; replacement continuations cannot cross a
   modified row or the removed state. Exterior tape is unchanged.

All replacement first actions write 0 or 1, move L or R, and enter an
existing working control. The radius is five and the replacement-path
budget is 500 transitions. Each check requires exact control, displacement,
and complete window contents at the join. All three output lists are empty.
An additional screen padded the earlier branch-pruned radius-five windows
with three independent arbitrary bits on each side, giving radius eight and
a 2,000-transition budget; the common-action and two-step screens again
found no witness. Padding enlarges the execution window but adds no assumed
context information.

Replay the three strongest local screens (C++17 compiler required):

    python3 run_local_screens.py

The script checks all inputs, compiles the three enumerators, and writes
fresh empty witness lists and a summary under local_replay/.

BOUNDED GRAMMAR SEARCH
----------------------
The grammar search expands formerly opaque source macros into known
subroutines, especially push-plus-copy and the two cons components. It can
reuse any existing fixed right-reading pair, rotate individual occurrences
as well as shared DAG nodes, count actually reachable fixed controls, and
permute parameter labels independently within the six axiom heads. The
h6 premise-exchange construction was tested with the primary, cached,
symmetric cached, zero-guard, and combined symmetric/zero fixed controllers.
The unchanged h6 grammar gives 194 states on each of these fixed bases.

The retained logs record 15,895,250 proposal slots in completed runs and at
least 4,572,000 additional slots before interrupted runs. A slot is not a
distinct machine, an accepted mathematical construction, or an exhaustive
search node. No run produced an accepted machine below 194 states; runs starting from
194 retained that count.
The numerical objective includes representation penalties and, in later
runs, a tie-break favoring deletion of fixed reader roots. In particular,
a scaled objective 600 ordinarily means 134 fixed plus 60 effective reader
states. A lower intermediate heuristic score would still require complete
source and physical validation. No new smaller endpoint was found.

search_summary.json gives exact per-run counters. grammar_search/ contains
small inputs, actual logs, and the C++ search programs. These are discovery
artifacts, unnecessary for validating the principal PA194Q construction.
The time-bounded searches need not stop at identical iterations on another
computer, even with the same seed. None of these searches proves global
minimality or exhausts all materially different 193-state designs.

PROVENANCE
----------
The generic physical executor, legacy interface map, and common-action
merger derive from the supplied PA194/PA194C research packets. Their
original provenance and licensing remain in the parent archive. The new
parts here are the finite ternary invariant, source/seed binding, invariant
specialization of the physical context collector, multi-predecessor
state-deletion and local-rejoining screens, and expanded-macro search
extensions. See files.sha256 for the frozen file identities.
