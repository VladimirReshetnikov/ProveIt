# Supplemental runtime and initializer searches

This packet preserves the root investigation's additional search programs,
their recorded results, and portable replays. **It does not contain a certified
217-state machine with the requested blank-tape equivalence.** The 217-state
table used here is the initialized interpreter supplied in `../core217/`.
Its primitive-interface proof and its failure to initialize itself are separate
questions.

## Reproduce

The packet needs Python 3 and a C++17 compiler. It uses only files included in
the containing investigation archive. The following commands assume this
directory is named `root-search` and the shell is at the archive's top level:

```sh
python root-search/run.py --packet-root . --output /tmp/zfc-root-smoke smoke
python root-search/run.py --packet-root . --output /tmp/zfc-root-search complete
python root-search/run.py --packet-root . --output /tmp/zfc-root-search onespare
python root-search/run.py --packet-root . --output /tmp/zfc-root-search two-row
python root-search/run.py --packet-root . --output /tmp/zfc-root-search runtime-rewrites
python root-search/run.py --packet-root . --output /tmp/zfc-root-search single-initializers
python root-search/run.py --packet-root . --output /tmp/zfc-root-search paired-initializers
python root-search/run.py --packet-root . --output /tmp/zfc-root-rejected check-rejected
```

`all` runs the smoke checks and six search commands. The optional
`check-rejected` task reconstructs and rechecks all 40 rejected preliminary
folds. To use the newly generated edit catalog for an initializer replay, add
`--edits /tmp/zfc-root-search/runtime_rewrites.txt`. The default catalog is the
recorded 492-entry catalog in `data/`. `--cxx` selects a different compiler.
All generated files go to `--output`; paths in the executable Python programs
are resolved from explicit arguments. The wrapper checks the hashes of the
baseline table, source sites, and 217-state initialized core before running.

The fast `smoke` command demonstrates three concrete facts:

1. The unchanged public 218-state table reaches its expected initial frame
   after 312,909 steps, at head position −5, with logical registers
   `[3,0,0,0,3,0,0,0,0]`, gap 80, and 130 spare words.
2. The preliminary fold of state 166 into state 12 fails a complete primitive
   test. The baseline visits dispatcher state 84 at steps 150 and 318 while its
   frame is still incomplete; its true return is at step 596.
3. Changing row 51/0 of the 217-state core to `1 L 6` produces a different
   raw initial frame, but fails a primitive test that respects the proven
   source masks and uses only one-valued spare words.

## Recorded search scopes

| Search | Domain and candidate family | Recorded result |
|---|---|---:|
| Complete-frame folds | 23,653 unordered pairs; inherited keeper rows, plus arbitrary synthesis of the other row when exactly one mapped action agrees | 322,028 specifications; 0 survivors |
| Complete-frame folds with one-valued spares | Same family; spare values fixed to 1 and lengths 1–5 | 322,028 specifications; 0 survivors |
| Fold 301 into 88 plus helper | Synthesize row 88/0 and one additional row encountered on the first failing path | 7,116,941 assignments tested; 0 survivors |
| Single-row edits of initialized core | Every alternative write, direction, and retained target for each of 434 rows; runtime domain excludes initialization | 378,014 edits; 492 finite survivors |
| One surviving edit, every start state | Each of 492 edits × each of 217 working states, blank tape | 106,764 cases; all classified as outward self-loop rays |
| Two surviving edits, start state 0 | Unordered pairs acting on distinct rows | 118,928 cases; 118,838 rays, 90 finite limits, 0 frames, 0 halts |

The first four rows are **finite discovery filters**. They require a join
within a bounded local window and bounded number of steps. A rejected local
join may still be compatible with a different global simulation argument.
These results are not lower bounds on machine size and do not exhaust possible
encodings. The 492 edits have passed only this finite filter; the packet does
not claim unbounded correctness for them.

The initializer programs use a 1,500,000-step limit and a finite simulation
array. Their `ray` classification has a separate elementary justification:
the head is outside the current finite tape support, reads zero, and takes a
self-loop moving farther outward. Induction then gives an infinite run through
fresh zero cells. A `limit` classification has no such meaning: all 90 limited
paired-edit runs remain unresolved by this search.

The complete-frame context generators cover 30,835 concrete cases: five
register assignments at each source primitive, with both branches of each
conditional decrement. They use radius-nine windows. The ordinary public
table run takes 17,602,319 transitions and yields 185,553 windows before blank
initialization is added. The 217-state core run takes 17,603,079 transitions
and yields 185,633 windows. These are concrete samples, not quantified register
domains. The generic spare values are 0,1,2,3,4; the separate `onespare`
generator fixes every spare value to 1. Public startup contributes all its
312,909 pre-initial-frame configurations to each fold domain.

## Correction to the preliminary search

The first context collector stopped at the first return to state 84. Some
primitive implementations visit that dispatcher before restoring a clean
frame. This omitted necessary portions of those primitive executions and
produced 40 apparent fold successes. The independent symbolic checker rejected
all 40. An earlier report of 25 rejections was an interim snapshot; the final
`results/hit_checks.json` contains 40 completed `REJECTED` records.

`REJECTED` means a proof obligation did not close. It is not itself a concrete
semantic counterexample. The first fold has an explicit counterexample:
source site 3126, instruction `CI3`, all nine registers zero, spare list `[0]`,
and gap zero. The baseline completes correctly in 596 steps; the folded table
returns an incorrect frame in 626 steps. The full trace and expected tape are
in the smoke output. The corrected context collectors continue to a complete
clean-frame return and yield zero survivors in both 322,028-specification
searches.

The 40 historical fold specifications are preserved in
`data/rejected-folds.json`. `code/check_hits.py` reconstructs each table from
the public baseline, applies its two keeper actions, and invokes the same
symbolic primitive checker. It does not rely on absolute filenames in old
logs. Historical logs and exact original scripts are retained as provenance;
the `archive/` scripts contain original workspace paths and are not the
portable entry points.

## Alternate raw initial frame

The exploratory table in
`results/raw-frame-diagnostic/raw-frame-exploration.native.tm` changes only
row 51/0 of the initialized 217-state core to `1 L 6`. From a blank tape it
reaches a clean frame after 532,731 steps at head position −17, with gap 1,
registers `[0,0,1,0,0,0,0,0,0]`, and 253 spare words. The spare values are
73 zeros followed by 180 ones. This is a recorded observation, not a calibrated
candidate.

The source-mask test fails at source site 0 (`CD8`, address `000`), on the
positive branch, from registers `[1,0,0,0,0,0,0,0,1]`, spare list `[1]`, and
gap zero. After 4,738 steps the resulting frame differs from the primitive's
specified result. The exact mask certificate, starting tape, expected tape,
actual tape, and complete execution trace are bound in the diagnostic JSON.
This prevents inheriting the existing masked primitive theorem. It does not
settle all behavior from the alternate seed; that would need a separate
reachable-state argument.

## Files and provenance

- `code/`: portable Python searches, parametric C++ generators/simulators, and
  the unmodified inherited `filter_source.py` and `check_joint_fold.py` helpers.
- `data/`: the 492-edit catalog, the 40 rejected fold specifications, and the
  first rejected native table used by the concrete diagnostic.
- `results/`: historical receipts plus portable replay results and traces.
- `archive/`: exact original root search scripts for comparison. The only
  behavioral-neutral C++ reporting change in `code/rewrite_init_search.cpp`
  adds a final census line, eliminating ambiguity from periodic progress logs.
- `SUMMARY.json`: machine-readable scope and counts.
- `MANIFEST.sha256`: checksums for the packet files, excluding itself.

The core's unbounded primitive proof is in the containing archive's
`core217/`; source-mask closure is in `machine-search/`. Neither is replaced
by the finite tests in this directory.
