# State-reduction searches around the 246-state table

This package records an attempted reduction of the supplied context246 machine.
**It does not establish a ZFC consistency machine with fewer than 246 states.**
It contains an exact permutation census, bounded state-identification searches,
and a new nine-state arithmetic core with a universal local proof and a proved
failure to integrate with the existing program counter.

The arithmetic result is useful for further compiler work, but it is not a
245-state consistency machine. No `.tm` file for the failed composition is
presented as a candidate deliverable.

A subsequent source reassociation and control-repair investigation is recorded
in `ROTATION_CONTROL.md`. Its 76,777,120 second-row repair proposals yielded no
full finite survivor. The explicitly named `failed` and `unrepaired` tables in
that investigation are counterexample artifacts, not consistency machines.

## Baseline and dependencies

The input is the `zfc-context246` package contained in ProveIt's incoming
`zfc-context246-20261018.zip`, read at ProveIt commit
`8cdc55ff9281b0aaba49bf74b0b225d57f12b893`.
The original-label table used by every recorded search is
`machine/zfc_prefix246_old.tm`, SHA-256
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

The fixture generator and local induction adapter import the package's
attributed literal instruction checker and symbolic induction checker.
The input register program is `sources/Prog254.v`, SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
The additional interval fixture set uses the separate, newly computed
`interval-invariants.json` from the main research package. A value upper bound
of 9 in that file denotes infinity. A finite witness is chosen within every
admitted interval; this does not assert that every such witness is reachable.

All C++ programs require C++17. Python scripts require Python 3 and the vendored
context246 Python code, with no third-party package. Assertions must be enabled.

## Results and their scope

| Search | Candidates | Finite survivors | What was established |
|---|---:|---:|---|
| All physical register permutations | 362,880 | 0 reductions | Every table has 246 exact state-bisimulation classes and all 246 working states are graph reachable from state 95. |
| Direct folds, unrestricted first-occurrence fixtures | 60,270 | 346 | Finite discovery screen, with 4,000 steps per fixture. |
| Those 346 folds, complete unrestricted instruction fixtures | 346 | 0 | No finite survivor over 8,391 guarded instruction fixtures, with 10,000 steps per fixture. |
| Direct folds, interval-admitted first-occurrence fixtures | 60,270 | 276 | Finite discovery screen respecting the new interval invariant. |
| Those 276 folds, all interval-admitted instruction fixtures | 276 | 0 | No finite survivor over 8,385 guarded instruction fixtures. |
| Direct folds with arbitrary new head, gap at least 40, and spares | 60,270 | 295 after the first screen, 0 after the second | Relaxes exact tape identity to equality of the logical frame; still only bounded discovery. |
| Remove 255 and edit one additional core row | 4,321,800 | 0 | Twelve representative arithmetic cases, at most 600 steps each. |
| Targeted two-row core synthesis after 255→131 | 37,402,680 second-row proposals | 1 local core | The surviving local contracts are universally checked; the global composition is proved to fail. |
| One additional exit-row edit of that core | 7,840 | 0 | No finite survivor, including a variant allowing arbitrary new head, gap at least 40, and spare suffix. |

The exact permutation result is an exhaustive finite statement about this
specific family and exact state bisimulation. It is **not** a lower bound on
the number of states needed to compute the same function, recognize the same
halting condition, or start from a blank tape.

Every directed-fold decision has its category, decisive fixture index, step
count and observation of a wrong expected return boundary recorded in CSV.
The categories `fuel_bound` and `tape_bound` are inconclusive. An unexpected
halt is a concrete failure of that selected instruction contract. A wrong
intermediate boundary is recorded, but not itself treated as a proof that the
machine could never rejoin the expected computation later.

The unrestricted first stage records 2,079 tape cutoffs, 133 unexpected halts,
and 57,712 fuel cutoffs. Its second stage records one unexpected halt and
345 fuel cutoffs. The interval first stage records 2,182 tape cutoffs, 218
unexpected halts, and 57,594 fuel cutoffs; its second stage records one tape
cutoff and 275 fuel cutoffs. Under the more permissive frame comparison,
295 first-stage survivors reduce to one tape cutoff and 294 fuel cutoffs.
None of these cutoff counts is an impossibility theorem.

## New local result: a nine-state arithmetic core

Remove state 255 and make these two edits to context246:

| Row | New transition |
|---|---|
| 75 / 0 | write 0, move R, enter 63 |
| 48 / 0 | write 1, move L, enter 131 |

The arithmetic states are
`48, 63, 73, 75, 83, 95, 109, 112, 131`.
All four inherited one-block traversal identities remain valid. For
`B(v) = 0 1^(v+1)` and a marked selected register in
`B(A) 00 1^x B(S)`, let `p = width(A)` and
`w = width(A ++ [x] ++ S)`. The induction adapter checks:

- **Positive decrement:** for `x > 0`, state 95 returns in state 48 after
  `2p + 4` steps; the origin moves one cell right and the selected value
  decreases by one.
- **Zero decrement:** with a following block, state 95 returns in state 112
  after `2p + 7` steps; the complete file is restored.
- **Increment:** state 73 returns in state 48 after `2w + 7` steps; the
  selected value increases by one and a value-zero spare is appended.

These are universal identities over arbitrary natural register values,
arbitrary finite prefix and suffix lists, and arbitrary untouched left
context. They are not extrapolated from the twelve synthesis tests. The
mathematical induction checker uses literal table rows, unary-loop induction,
finite-list induction, and the word identity `C(A)1 = 1B(A)`.
It is not a new Lean or Rocq endpoint.

The new zero-decrement path visits state 48 before rollback is finished.
The original checker's eager free-word normalization at every such visit
obscures the carried prefix. The adapter disables that *optional word rewrite*
for the zero-decrement proof, which does not need it, while keeping every
literal transition and induction rule unchanged. It reenables the proved
identity for the increment proof.

### Why the composition fails

The four states `48, 63, 112, 131` form a closed component after the edit.
Every one of their eight transitions moves left and returns to that component.
From blank tape, start state 95 enters it after three literal steps:

`95 → 109 → 75 → 63`.

Induction therefore proves that this modified blank computation never halts
and never resumes the proof-search dispatcher. The old program-counter
increment entry through `48 / 0 → 7` has been consumed by the arithmetic
optimization. A local saving of one state has not yielded a saving for the
whole consistency machine. The same verification script checks both the local
identities and this global obstruction.

The remaining concrete compiler problem is to provide a program-counter return
with at most the already available states while retaining the new spare-zero
tail. A valid solution must break the closed component in a way that also
preserves all instruction cases and supplies a correct blank initialization.

## Reproduction

Use explicit paths to the vendored baseline and interval certificate:

```sh
CONTEXT246=/path/to/vendor/context246
INTERVALS=/path/to/results/interval-invariants.json
```

Regenerate both fixture sets:

```sh
python code/capture_cases.py --baseline "$CONTEXT246" --output results/unrestricted
python code/capture_cases.py --baseline "$CONTEXT246" --intervals "$INTERVALS" --output results/interval
```

Compile and run the direct-fold screens. Both executables print surviving
ordered state identifications as `PASS old replacement`; the CSV side file
contains every decision and has a `.summary.json` companion.

```sh
c++ -O3 -std=c++17 code/directed_folds.cpp -o /tmp/zfc-directed-folds
/tmp/zfc-directed-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/unrestricted/micro-contexts.txt 4000 micro results/unrestricted/micro-decisions.csv all > results/unrestricted/micro-survivors.txt
/tmp/zfc-directed-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/unrestricted/whole-instructions.txt 10000 full results/unrestricted/whole-decisions.csv results/unrestricted/micro-survivors.txt > results/unrestricted/whole-survivors.txt
/tmp/zfc-directed-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/micro-contexts.txt 4000 micro results/interval/micro-decisions.csv all > results/interval/micro-survivors.txt
/tmp/zfc-directed-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/whole-instructions.txt 10000 full results/interval/whole-decisions.csv results/interval/micro-survivors.txt > results/interval/whole-survivors.txt
```

The semantic-frame variant changes only its final comparison: it permits any
head coordinate, any gap at least 40, and any nonempty spare suffix, with the
same logical program counter and nine register values.

```sh
c++ -O3 -std=c++17 code/semantic_frame_folds.cpp -o /tmp/zfc-semantic-folds
/tmp/zfc-semantic-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/micro-contexts.txt 4000 micro results/interval/semantic-micro-decisions.csv all > results/interval/semantic-micro-survivors.txt
/tmp/zfc-semantic-folds "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/whole-instructions.txt 10000 full results/interval/semantic-whole-decisions.csv results/interval/semantic-micro-survivors.txt > results/interval/semantic-whole-survivors.txt
```

Reproduce the exact permutation census and universal local core proof:

```sh
c++ -O3 -std=c++17 code/permutation_bisim.cpp -o /tmp/zfc-permutation-bisim
/tmp/zfc-permutation-bisim "$CONTEXT246/machine/zfc_prefix246_old.tm" > results/permutation-bisim-output.txt 2> results/permutation-bisim-summary.txt
python code/check_shared_core.py --baseline "$CONTEXT246" --output results/shared-core-proof.json
```

Optional bounded synthesis searches:

```sh
c++ -O3 -std=c++17 code/core_mutations_all.cpp -o /tmp/zfc-core-one-edit
/tmp/zfc-core-one-edit "$CONTEXT246/machine/zfc_prefix246_old.tm" 600
c++ -O3 -std=c++17 code/core2_search.cpp -o /tmp/zfc-core-two-edit
/tmp/zfc-core-two-edit "$CONTEXT246/machine/zfc_prefix246_old.tm" 500 131
c++ -O3 -std=c++17 code/core3_global.cpp -o /tmp/zfc-core-exit
/tmp/zfc-core-exit "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/whole-instructions.txt 10000
c++ -O3 -std=c++17 code/core3_global_semantic.cpp -o /tmp/zfc-core-semantic-exit
/tmp/zfc-core-semantic-exit "$CONTEXT246/machine/zfc_prefix246_old.tm" results/interval/whole-instructions.txt 10000
```

The targeted two-edit search fixes `255→131`, chooses its first changed row from
the six rows visited by the failed baseline zero case, and intersects the
row-visit masks of failed concrete tests to choose the second changed row.
It stops at the first expected macro return boundary and uses a 500-step limit.
Those restrictions define a bounded synthesis family; they do not exhaust all
possible two-row modifications of the entire machine.

## Contents

- `results/search-summary.json`: compact consolidated results and scope.
- `results/*/summary.json`: fixture provenance and counts.
- `results/*/instruction-metadata.json`: source instruction, guard and exact
  chosen physical register values for every fixture.
- `results/*/micro-contexts.json`: exact source and target supports, with the
  program index and literal source-step number for each first occurrence.
- `results/*/*-decisions.csv`: all state-pair decisions, including cutoffs.
- `results/permutation-entry-whitelist.json`: the 14 selector-entry rows
  retargeted in the exact permutation census.
- `results/shared-core-proof.json`: full symbolic proof traces and the proved
  closed-component obstruction.
- `search-findings.tex`: a manuscript section for incorporation in the main report.
- `ROTATION_CONTROL.md`: the later source-reassociation repair search, including
  a portable fixture generator, exact failed table, and complete literal trace.
