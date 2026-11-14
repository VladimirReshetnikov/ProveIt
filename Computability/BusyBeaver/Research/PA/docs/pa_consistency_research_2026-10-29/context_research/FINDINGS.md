# Context, runtime, and scanner reduction research

Status: **No accepted sub-208 candidate from the searches in this directory.**
The file `u207_sixzero.native.tm` is an explicitly REJECTED exploratory machine,
not a deliverable candidate. Its failure is recorded in `sixzero_failure.json`.

## Baselines

The principal native table is the History archive's class-A U208:

`extracted/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine/u208.native.tm`

SHA-256: `36b58fea7a184b1050914170e8f5240c8a13da218dbbfa7e1985cd73d516e5c7`.

The structurally distinct class-B table was taken from the same archive's
`machine/compatibility_variant/u208.native.tm`, with its own source sites.
The five supplied archive proposals reduce to two relevant transition graph
classes; the separate comparison audit owns that classification.

## Fixed-point finite-window invariants

A new finite abstract transition system tracks a state and the `2r+1` tape
bits surrounding its head. Every step updates the current bit, shifts the
window, and admits BOTH values for the newly exposed boundary bit. Starting
with every possible window at state 0 gives a sound overapproximation of all
runs from state 0, on arbitrary initial tapes. Iterating to a fixed point
uses unbounded history, unlike the previous depth-k suffix enumeration.

Results:

| Baseline | Radius | Possible state/window pairs | Reachable abstract pairs | DNF cubes |
|---|---:|---:|---:|---:|
| A, arbitrary initial tape | 7 | 6,815,744 | 961,765 | 2,692 |
| A, arbitrary initial tape | 9 | 109,051,904 | 11,318,840 | 7,796 |
| B, arbitrary initial tape | 7 | 6,815,744 | 967,781 | 2,698 |

`window_reach.cpp` discovers these sets. `window_contexts.py` converts them
to a disjoint decision-diagram path cover. `check_window_invariant.py`
independently checks initial inclusion, both successors for every abstract
transition, and exact equality with the DNF representation. The radius-7
class-A certificate passed 1,923,274 successor checks, and its receipt is
`window7all_checked.json`. This is a finite executable invariant check,
not a proof-assistant kernel certificate. The mathematical soundness
argument is ordinary induction on the run length.

The binary `.bin` arrays are intermediates. Do not include all of them in a
small research archive: they are reproducible from the C++ source, or can
be losslessly compressed. The 109 MB radius-9 array is not needed to check
an accepted construction, since this branch found none.

## Search outcomes and exact scope

1. **Direct same-head aliases:** depth-8 history and the fixed-point
   contexts found no exact local alias. A separate dual-block alias search
   permitted positive old and new blocks up to 45 transitions and accepted
   any two halting endpoints, regardless of tape/head. No exact survivor
   occurred on A or B.
2. **One-row representative folds:** the fixed-point class-A radius-7
   search found no accepted one-row fold (macro bound 35).
3. **Broader two-row synthesis screen:** class A screened 35,588,268
   replacement trials for separately synthesized representative rows with
   one-step old simulation; no finite survivor occurred. This is NOT an
   exhaustive search over all coupled two-row modifications.
4. **Two-row synthesis with positive blocks on both sides:** class A
   screened 36,412,128 row candidates and generated 2,454 sampled composite
   survivors. All failed the exact symbolic check against the complete
   radius-7 context families. Class B screened 36,190,224 candidates,
   generated 1,396 sampled survivors, and rejected all symbolically.
   The block bound was 19 on each side. The synthesis separates the row
   candidates before combining them, so it may miss essential coupling.
5. **Head-offset aliases:** for a deleted state whose incoming moves are
   all d, flip the incoming directions and use the relation
   `(q,h,T) ~ (r,h-2d,T)`. On A, 36,639 aliases were rejected, with macro
   bound 41. A one-row representative synthesis screened 60,674,184
   mutations. Its only two finite survivors were unchanged representative
   rows for deleting state 1 into state 2; both failed the exact symbolic
   context `state 1, read 0, {T(0)=0}`.
6. **Tape-tag aliases:** flip each incoming written bit, optionally also
   the direction. The relation complements cell `h-d` and optionally
   shifts the head by `-2d`. None of 73,278 class-A aliases survived.
7. **Direct aliases checked by complete primitive endpoints:** this
   intentionally removes the local bounded-macro restriction. Of 42,642
   ordered pairs (deleting native 0 and 84 excluded in this particular
   driver), 23 passed selected primitive cases covering the removed state;
   all failed the full 15,252-case, three-assignment regression suite.
   The baseline suite passed 6,771,470 literal transitions. Each changed
   case had a conservative 5,000-step execution cap, verified sufficient
   for the baseline finite suite. The cap is a search limitation.
8. **One-row folds checked by complete primitive endpoints:** 468
   compatible ordered state/read-row pairs and 389,376 modifications,
   including the distinguished halt target, were tested on each class.
   Class A had 26 targeted survivors and class B had 32; none passed the
   full 15,252 finite contracts. Here deleting either native 0 or 84 is
   allowed; when deleting 84, the canonical entry and exit state are
   translated to its representative. Startup would still need checking
   for any successful candidate.
9. **Moving the halt row:** deleting native 68 into 196 shares their
   `read 0 -> 0 R77` row. We tested 343,616 changes combining a new
   196/read-1 behavior with one other retained row changed to halt.
   All failed selected full-primitive tests. CH contracts accept any
   halting tape/head. Final halt writes and moves are irrelevant here,
   so one fixed `0 R254` halt row suffices for this search family.
10. **Two-row scanner repair:** after deleting native 34, replace 23/read-0
    arbitrarily and also change one row of a retained scanner state in
    `{1,2,3,5,9,15,23,75}`. The search admitted arbitrary writes, either
    move, and any retained working target, including helper excursions.
    It checked 828 single patches and 5,832,432 pairs against 5,093 distinct
    full-tape entries into state 1, collected from 500 primitive sites
    under three assignments. No candidate preserved the exact old first
    return to state 84 within 600 steps per entry. This is finite evidence
    about preserving that routine, not a lower bound for the overall task.

The exact symbolic case checkers compare complete tapes on every branch;
unread exterior cells remain formal unknowns. Nevertheless, negative
bounded search results are not lower bounds on the possible state count.
All global primitive checks in items 7-10 are finite regression evidence,
not proofs for arbitrary register values or for the complete blank run.

## Why the tempting six-zero scanner is wrong

Delete native 34 and replace `23 0 0 L34` with `23 0 0 L75`.
This has 207 working states and looks plausible because the source
leaf words and their control-flow successors have internal zero runs at
most five after stripping trailing zeros. The argument is false: transient
runtime program-counter words matter.

Use the first primitive, `CD 8`, at source address `000000`, with all nine
registers zero, one zero spare, gap zero. At its second internal dispatcher
return the tape has ones at

`{-1} union {7,...,56} union {58,62,64,66,68,70,72,74,76}`.

The seven zero cells 0 through 6 lie between the anchor and the temporary
one block. The old scanner reaches native 23 at head 1, then executes

`23/0 -> 34 at head 0 -> 75 at head -1 -> 84 at head 0`.

The modified scanner instead executes

`23/0 -> 75 at head 0 -> ... -> 75 at head 7 -> 84 at head 8`.

The tape agrees exactly, but the dispatcher head is displaced by eight
cells. Thus trailing source zeros cannot be discarded from the bound.
A decrement-zero primitive can add a temporary zero to that suffix.
`sixzero_failure.json` retains the full two traces and complete endpoints.

## Reproduction notes

All discovery outputs are in this directory, separate from untouched
extracted source archives. C++ programs use C++17. Python scripts need the
standard library except the independent window-invariant checker, which
uses NumPy for exhaustive finite set operations. Sources adapted from the
input archives retain their original names and docstrings; the new
fixed-point discovery, offset/tag searches, full-primitive searches, and
scanner repair are the additions in this research branch.

No file in this branch should be described as a proved 207-state Con(PA)
machine. The remaining candidates being investigated by other agents are
independent of these negative results.

## Final global endpoint extensions

The global endpoint fold search was also repeated on five finite-validated
source reassociations, each retaining the original startup-used rows and
source ordinal 136 address. None yielded a finite survivor. Their class-A
layout labels39,79,119,159,199 respectively screened 394,368; 396,032; 394,368;
392,704; and 394,368 modifications against all 15,252 finite primitive contracts.

An append-zero-spare backend variant was checked separately: 391,040 one-row
folds and 43,056 direct state aliases found no finite survivor under the
modified CI postcondition. This does not independently establish the
variant's blank startup calibration.

A stronger global screen uses the supplied 278,384-state zero/positive source
invariant and the independent register6 trit invariant. Simply discarding
incompatible members of the old 15,252-case suite left only 3,337 cases; 22,230
spurious folds passed because whole source routines were absent. Those
results were not accepted. Instead, a new 71,622-case corpus covers every
source ordinal admitted by the intersection, with multiple admissible masks,
all admitted CD branches, three positive-value choices, and all spare blocks
set to one. Of 389,376 class-A modifications, 48 survived selected cases and
none survived the full 71,622 corpus. Therefore no candidate reached the
proposed 835,152-case exhaustive-mask followup.

The same 71,622-case construction was applied to class B and all five safe
alternative layouts. The final counts were:

| Input | Modifications | Targeted survivors | Full survivors |
|---|---:|---:|---:|
| A |389376|48|0|
| B |389376|22|0|
| layout39 |394368|64|0|
| layout79 |396032|4|0|
| layout119 |394368|58|0|
| layout159 |392704|76|0|
| layout199 |394368|56|0|

The capsule includes the portable class-A driver and frozen input invariant
files. Their mathematical source-invariant proofs belong to the accompanying
source-optimization packet. The context capsule's default checker verifies
its own window invariant and scanner counterexample; it does not claim to
re-prove that separate source analysis. All these endpoint searches are
finite and bounded. Different C++ standard-library shuffle implementations
can change which sampled masks are chosen; the exact reported numbers are
from the supplied GCC/libstdc++ run.
