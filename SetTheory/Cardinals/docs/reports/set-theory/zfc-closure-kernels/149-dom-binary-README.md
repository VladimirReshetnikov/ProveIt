# The 218-state machine: exact table and portable validation

This directory contains the exact binary, one-tape machine compiled from source
`source_0059.json`, together with deterministic reconstruction and a mathematical
runtime checker. The machine has **218 working states and one distinguished halt
state**, 436 transition rows, moves only left or right on a two-way infinite
tape, and starts on the entirely zero tape. The native-label initial state is 0
and its halt label is 254.

The equiconsistency theorem and the source compiler correctness argument belong
to the accompanying research report. This subpackage establishes the separate
low-level obligations: a complete literal transition table, the blank-start
trajectory, and the specified register primitive at every source address for
all natural register values.

## Files

- `machine/k218.native.tm`: exact table used by the runtime proof checker.
- `machine/k218.compact.tm`: identical machine with working labels 0 through
  217 and halt label 218; initial label 0. The relabeling lists native working
  states in increasing order, with the initial state first.
- `machine/sites218.json`: all 4,751 leaves of the complete source prefix tree.
- `machine/transition_recipe.json`: exact edits to the included baseline219,
  native-to-compact map, and byte-level SHA256 hashes.
- `machine/k219.baseline.native.tm`: the pinned repository baseline needed by
  the direct transition recipe.
- `code/validate_native.py`: portable standard-library driver for blank startup
  and the complete arbitrary-natural runtime proof.
- `code/rebuild_table.py`: deterministic reconstruction from the baseline and
  transition recipe. No optimizer or solver is needed.
- `code/runtime/`: the two mathematical runtime modules, copied verbatim from
  the prior whole-tape runtime audit.
- `validation/runtime.json` and `runtime_cases.json`: summary and all 6,176
  successful quantified primitive derivations.
- `validation/startup.json`: the complete 312,605-transition blank-start trace.
- `validation/boot_boundary.json`: the resulting whole-tape frame without the
  large transition list.
- `validation/portability.json` and `portable_runtime.json`: a second complete
  replay from this folder under isolated Python; all case and startup receipts
  were byte-for-byte identical to the original validation.
- `provenance/`: allocation and preservation records, including the intermediate
  `unfolded221.reference.tm` whose complete startup trajectory was preserved;
  these are informative and are not required to rerun the table proof.

## Replay

Use Python 3.10 or later, with assertions enabled. From this directory:

```sh
python code/rebuild_table.py machine/k219.baseline.native.tm machine/transition_recipe.json rebuilt.tm
python code/validate_native.py machine/k218.native.tm machine/sites218.json replay_results
```

The first command reports `EXACT_RECONSTRUCTION_PASS 218 working states`.
The second command reports `CALIBRATED_DIRTY_ROOT_SEED` at step 312605 and
`UNIVERSAL_MATHEMATICAL_PASS` with 6176 proved cases. A full run normally takes
roughly two minutes, depending on processor availability. Its output recreates
the detailed receipts. The supplied native-label table, rather than the compact
relabeling, is the input to this particular checker, whose four list-lemma entry
names use the historical labels.

## Exact verified statements

The blank execution reaches dispatcher state 84 with head position -5, zero
program counter, and logical primary register vector

```text
[N,T,W,A,D,H,X,Y,L] = [3,0,0,0,3,0,0,0,0].
```

The complete remaining tape is recorded in `boot_boundary.json`. The root seed
has all three formula-bearing fields zero, and the source calibration theorem
allows the nonzero values of N and D.

For each of the 4,751 source addresses the runtime checker derives the full
tape transformation of its primitive. Both decrement guards are considered,
giving 6,176 cases. Every primary register value is an independent natural
number; the extra header gap is an arbitrary natural number; the spare blocks
form an arbitrary nonempty finite list of arbitrary natural values. The tape
has its entire zero exterior represented. The proof rules are literal machine
transitions, induction over unary lengths, and structural induction over the
spare-block list. The four list lemmas are derived again from the exact supplied
table before the cases are checked.

These are executable mathematical derivations rather than a proof-assistant
kernel certificate. A finite symbolic proof-construction bound does not impose
a bound on the represented natural values, machine runtime, gap, or spare-list
length. A failed proof search would be reported as `NOT_PROVED`, not as a semantic
counterexample. The source-level equiconsistency theorem is an additional
obligation, proved separately in the main report.

## State saving and provenance

The final source has 203 distinct syntax DAG nodes, depth 45, and maximum zero
run 6. Its 23 distinct primitive types contain no `CC 4`; allowing that primitive
during search helped find a new source association but it is absent from the
final source. The machine has 168 physical decoder states and 50 other working
states. Relative to the supplied 219-state baseline, native states 227 and 228
are removed, native state 400 is added, and the recipe changes the decoder rows.
All 246 rows used by the blank-start trajectory of the intermediate unfolded
221-state reference are preserved verbatim. That reference expands two decoder
aliases before the new source is allocated. Its startup, and that of the final
218-state table, takes 312605 transitions; the original 219-state table takes
312617 transitions to the same boundary. No new initialization state or extra
zero-run detector stage is needed in the final machine.

The baseline comes from repository commit
`f8ec6158f3bdc885139ee395ae34fe44c3251b9f`, at
`Computability/BusyBeaver/Research/ZFC/candidate-k219/k219.native.tm`.
The baseline table SHA256 is
`b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.
The final native table SHA256 is
`9c8505bf3731212192b83ee61dbc569085b4675ae9e0539843ae57d43ad9e886`.
The source-address table SHA256 is
`264fba90229974a53c2c5c943cf5fe8924327b6bbc31bd47e64d7f5c670b7495`.
All other included file hashes are listed in `manifest.json`.
