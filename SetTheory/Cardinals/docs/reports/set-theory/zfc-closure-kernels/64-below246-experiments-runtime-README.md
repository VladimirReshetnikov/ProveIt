# Runtime reduction experiments against context246

**Result:** this directory does not contain a new machine satisfying the
requested consistency equivalence. It contains reproducible finite searches
and a concrete counterexample to an attractive contextual fold. The searches
leave no complete candidate in the families described below. They do not
establish a lower bound on the number of states.

All state numbers use the original labels in
`machine/zfc_prefix246_old.tm`. This table has 246 working states, start 95,
dispatcher 96, and halt 254. The SHA-256 of the required table is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.
The Python entry points check this pin. No script edits the baseline archive.

## Reproduction

Python 3 and a C++17 compiler suffice. There are no additional Python package
dependencies. From an extracted archive containing this directory as
`experiments/runtime` and the baseline as `baseline/context246`, run:

```sh
export ZFC246_BASE="$PWD/baseline/context246"
python experiments/runtime/runtime_searches.py --family all
python experiments/runtime/run_single_entry.py
python experiments/runtime/verify_return_counterexample.py
```

Adjust `ZFC246_BASE` to the directory containing `machine/`, `sources/`, and
`code/`. If that environment variable is unset, the scripts use the original
workspace layout, `../../context246/zfc-context246` relative to this directory.
Every output stays beside the experiment sources. `run_single_entry.py`
rebuilds deterministic fixtures, compiles the C++ search in a temporary
directory, runs it, and records a summary. Use `--compiler g++` if needed;
`--skip-prepare` reuses existing fixtures. Running all searches takes roughly
one to two minutes on the development machine; timing is not part of the
result.

## 1. Repairing the sole external incoming transition

This search is broader than redirecting one target label. For each eligible
state `q`, the entire transition on its sole external incoming edge is
replaced: the write bit, move direction, and target state all vary. Self-loops
are not counted as external incoming edges. A candidate may target any of the
other 245 working states. Thus there are `2 * 2 * 245 = 980` recipes per
eligible state.

The start 95 and dispatcher 96 interfaces are held fixed. Of the remaining
states, 139 have exactly one external incoming edge. The final result is:

| Quantity | Value |
| --- | ---: |
| Eligible deleted states | 139 |
| Repairs per state | 980 |
| Total candidate repairs | 136,220 |
| Concrete instruction fixtures | 8,391 |
| Literal candidate fixture runs | 147,921 |
| Recipes passing their entire affected fixture set | 0 |

The fixtures include every one of the 6,460 compiled source instruction
sites, with both guards of each decrement instruction. Their primary
registers are `register[i] = i mod 4`, except that a selected decrement
register is set to zero or two. The spare registers are `[0,1]`, the head is
at 0, and the frame span is 48. Every fixture is first checked against the
unmodified baseline, including the complete final tape and expected head.
Both read bits occur for every eligible deleted state across the baseline
fixtures. This is contextual coverage, not an invariant about all executions.

For each deleted state, only fixtures whose baseline run enters that state
are re-executed. This omission is exact for this finite corpus: a run that
never enters the state cannot encounter the only altered external incoming
transition. Each candidate is checked at the fixed dispatcher 96 against the
complete expected successor tape, head, and halt behavior. It must pass
every affected fixture to survive. The screen uses 10,000 steps per fixture
and at most 15 unsuccessful visits to dispatcher 96.

These budgets matter. A rejection labelled `step_budget` or
`dispatcher_budget` is a failure of this bounded protocol; it is not an
unbounded non-equivalence proof. In particular, a hypothetical correct
candidate taking more steps would be discarded. The result says that no
recipe in this explicitly enumerated family met this finite acceptance
protocol. It says nothing about coordinated changes on several incoming
edges, different dispatch interfaces, or a new representation of registers.

The artifacts are:

- `single_entry_prepare.py`: constructs and verifies the source-site fixtures.
- `single_entry_search.cpp`: literal simulator and exhaustive recipe loop.
- `run_single_entry.py`: reproducible build/run driver and summary collector.
- `single-entry-summary.json`: counts, eligibility list, input hashes,
  rejection counts, and example rejected fixtures for each reason.
- `single-entry-fixtures.json`: human-readable frames, indexed from zero.
- `single-entry-table.txt`, `single-entry-cases.txt`, and
  `single-entry-members.txt`: exact C++ inputs.
- `single-entry-rejections.jsonl`: one bounded rejection record per recipe,
  as `[deleted_state, source_state, source_read_bit, new_write, new_move,
  new_target, fixture_id, reason]`; moves are -1 for left and +1 for right.
- `single-entry-survivors.jsonl`: empty in the reported run.
- `single-entry-search.log`: progress and the raw final count.

## 2. Nine directed runtime searches

`runtime_searches.py` gives one implementation of nine previously explored
families. Their fresh machine-readable results are in
`reproduced-searches/`. An action such as `1L131` means write 1, move left,
enter state 131. Every family varies all four write/direction choices and
every eligible target label, while holding the listed other rows fixed.

| Family | Fixed changes and varied row | Recipes | Survivors |
| --- | --- | ---: | ---: |
| `delete255` | Vary 75/0; target cannot be 255 | 980 | 0 |
| `delete75` | Vary 109/0; target cannot be 75 | 980 | 0 |
| `ones_tail` | 109/0=1R75, 75/1=1L33; vary 75/0, target not 255 | 980 | 0 |
| `ones_positive` | 109/0=1R75; vary 75/1, target not 255; positive decrement only | 980 | 2 partial |
| `branch48_tail` | 48/0=1L131, 131/0=0R7; vary 75/0, target not 255 | 980 | 0 |
| `fold2` | Delete 2, redirect its incoming targets to 4; vary 20/0 | 980 | 0 |
| `whole_zero_carry` | Delete 112 and 131; 255/1=0R95; vary 255/0 | 976 | 0 |
| `marked_zero_carry` | Previous family plus 75/0=0R255 | 976 | 0 |
| `shrinking_increment` | Delete 75 and 255; 109/0=0R48, 48/0=1L131; vary 131/0 | 976 | 0 |

The nine families comprise 8,808 recipes. The two `ones_positive` survivors
are `75/1=1L33` and `75/1=1L126`. They pass only the stated positive-decrement
fixtures and are not complete machines or evidence of a state reduction.
The first two deletion families have only one external edge into the state
being removed; their old rows can remain in the simulator because no other
retained state can enter them after the repair.

### Local macro acceptance

The first five families stop at the original runtime interfaces. They use
the marked unary word

`B(prefix) 00 1^selected B(suffix)`, where `B(v) = 0 1^(v+1)`.

Zero decrement must restore the complete register file and enter 112 at
head -1. Positive decrement must produce the original shifted file and
enter 48 at head 0. Increment must increase the selected register, preserve
the existing remaining register values and left context, and enter 48 at
head -1. Increment may append **any finite list of valid spare blocks**,
including no extra block. Thus this experiment does not unnecessarily
require an appended spare to have the original value 1.

The small local fixture lists and step budgets are recorded in each JSON
result. The screen also stops if the head crosses the left interface, if an
exact full configuration repeats, or if an increment exit frame is invalid.
The opaque left context is fixed to `[1,0,1]` for these experiments. This is a
finite protocol, not an induction over arbitrary words. In `branch48_tail`,
seven recipes pass the first zero-decrement fixture and all seven fail the
first increment fixture.

### Whole-instruction acceptance

The last four families use literal complete instruction runs at dispatcher 96
and inspect all four non-halting instruction kinds, with both decrement
guards. The first source sites of those kinds are selected deterministically
from `Prog254.v`. Primary registers are `register[i] = 3*i mod 7`; a selected
decrement register is set to zero or one. Spares are `[0]`, head 0, span 40.
Exact fixture ordering, read/write edits, and the first rejected recipe and
case are in each result JSON.

The target frame contracts allow the representation changes motivating
these families. `whole_zero_carry` permits zero decrement to shift the file
right by one and append a value 1 spare. `marked_zero_carry` permits the same
shift but no appended spare, and removes the usual increment spare append.
`shrinking_increment` permits increment to shrink the control gap by one
without appending a spare. The expected *logical* successor instruction
remains the source-program successor in each case. The whole-instruction
searches use at most 15 intermediate dispatch visits and either 5,000
(`fold2`) or 10,000 steps. Again, those limits are acceptance conditions, not
non-halting proofs.

## 3. A useful contextual identity, and its missing global premise

Consider these two changed transitions:

```text
48/0  = 1L131
131/0 = 0R7
```

If state 48 scans cell `h` containing 0 and cell `h-1` also contains 0, the
three-step path is:

1. Write 1 at `h`, move left to 131.
2. Preserve 0 at `h-1`, move right to 7.
3. State 7 erases the temporary 1 at `h` and moves left to 7.

This exactly matches the original one-step `48/0=0L7`, including head,
state, and every tape cell. No condition is needed on any other cell. The
identity therefore is a valid local lemma under the two-zero premise.

The controller does not supply that premise universally. The actual
source instruction at PC`0111` is an increment of logical register 0.
Starting with all nine primary registers zero, spare list `[0]`, head 0,
and span 40, the unmodified literal machine reaches state 48 after 362 steps
at head 4. Cell 4 is 0 but cell 3 is 1. The whole baseline instruction completes
correctly after 470 steps.

At this reachable intermediate configuration, the original one-step rule
ends in state 7 at head 3. The changed three-step path ends in state 112 at
head 1 and changes a different tape cell. Thus applying the local identity
without proving its left-neighbor premise is unsound. This is an exact
finite counterexample to that claimed premise, independently of any time
bound interpretation.

Run `verify_return_counterexample.py` to regenerate
`return-counterexample.json`, which contains the complete witness tape and
both endpoint traces. A larger redesign could change how the controller
reaches this configuration; this counterexample does not rule out all such
redesigns.

## Interpretation

These experiments identify specific obstructions. Removing a shared runtime
state requires preserving both the register transformation and the control
mode carrying the zero test back to the program counter. A local return
identity also requires an invariant at every actual caller. The separate
forward-carry experiment in the enclosing report proves a useful register
transformation, but its erased branch information prevents treating its
smaller table as a completed consistency machine. The present finite
searches complement those symbolic arguments; they do not replace them.
