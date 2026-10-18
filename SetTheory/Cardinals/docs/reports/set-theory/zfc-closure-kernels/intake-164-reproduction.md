# Recover and reproduce source 68

The full main replay **passed** in 535.016 seconds, with exit 0 and no timeout.
The expanded whole-frame pass completed all 8,391 cases and 2,312,645 symbolic
rules, covered all 490 rows, and proved minimum progress of 13 steps. Its
case records and covered rows exactly match the delivered certificate.
All other main gates passed, including 8,385 regenerated C++ fixtures (maximum
2,686 moves), and exact 407,915-step blank initialization. See the
[terminal record](data/intake-164-full-run-record.json),
[summary](data/intake-164-full-verification-summary.json), and
[raw output map](data/intake-164-fresh-output-map.json). Large fresh JSON outputs
are losslessly gzip-compressed; logs are retained with a `.txt` suffix.
The regenerated literal fixture equals the already retained compressed fixture;
the ephemeral compiled C++ executable is identified but not committed.

Placement `46e8518e0e` preserves 273 ancillary files. The original archive at
`8286787dd0468d848db345debe304b002d7064a4` also preserves the 21 manuscript,
PDF and delivery files. Restore all 294 payloads, with their original names,
outside the checkout:

```sh
python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/recover_164.py \
  --repo "$PWD" --output /tmp/zfc164-recovered
```

The package root is `/tmp/zfc164-recovered/zfc245-proof-20261018`.
Recovery reads the committed arrival ZIP and compares all 273 placed payloads
directly with it. It executes no delivered program and interprets no checksum
manifest. The [fresh recovery record](data/intake-164-recovery.json) passes.

Run the complete main verification on a further disposable copy:

```sh
env -u PYTHONOPTIMIZE python3 -B SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/replay_164.py \
  --package /tmp/zfc164-recovered/zfc245-proof-20261018 \
  --output /tmp/zfc164-full-replay --whole-frame --literal
```

Python 3.10+ and the standard library suffice except for `--literal`, which
requires `g++` or `clang++` with C++17 support. Assertions must remain enabled.
No Lean/Rocq compiler, solver, package installation or network access is used.
The default cap is 1,200 seconds for the whole suite. The helper records and
terminates the process group on timeout; failure and incomplete statuses must
not be reported as a completed verification.

The wrapper makes precisely the two copy-only adaptations recorded in
[the executed diff](data/intake-164-executed-adaptation.json): it omits the
delivery checksum-manifest blocks of `verify_all.py` and `verify.py`, as the
repository's intake procedure requires. All exact machine/source identities,
source-text adaptation checks, certificate byte comparisons and mathematical
assertions remain. The [independent adapter review](data/intake-164-adapter-review.json)
checks all 294 paths and finds exactly those two changed files. Delivered
sources are never patched. The flattened placed filenames are archival copies;
execute the recovered nested package, not those flattened scripts in place.

`--prepare-only` makes the copy, applies the adaptations and records the
planned command without executing it. The installed helper was checked this
way against the [independently reviewed preparation](data/intake-164-maintained-prepare-review.json).
The actual main run used an earlier root invocation of the same adapted
drivers. Its raw command, logs and terminal record are retained separately;
preparation is not a second proof replay.

## What the checks mean

The [driver review](intake-164-checker-review.md) lists every substantive gate.
The core rebuild reparses the original program, checks the 3,013-pair source
bisimulation, and checks all 8,391 guarded instruction cases. The next stage
rederives register macros on the actual table before a second full affine
replay. `--whole-frame` expands independent arbitrary primary registers and
an arbitrary nonempty spare suffix, while retaining proved unary/list rules.
It has no finite register bound or sampled gap bound. The 8,385 C++ fixtures
are separately labeled finite regressions, not universal premises.

Other gates check all residual pointers, the complete renumbering and printed
table, 54 bootstrap equations, 1,410 three-zero scanner contractions, and the
final machine's independent sparse/dense blank execution. An abstract grammar
audit's historical fixed-framework count of 118 does not include shortening
the scanner; its printed 246 is not the final literal table count.

## Supplemental investigations

On another writable copy of the recovered package, run these commands from
its root. Use fresh absolute output paths; the selector checker instead
refreshes its fixed local result file.

```sh
python3 -B research/architecture/verify_permutation_selectors.py
python3 -B research/architecture/verify_semantic_resegmentation.py --write-report /tmp/zfc164-semantic.json
python3 -B research/architecture/verify_affine_resources.py --recompute --write-report /tmp/zfc164-affine.json
python3 -B research/propositional/check_propositional_obstructions.py
```

All four freshly pass in the [auxiliary replay](data/intake-164-fresh-aux-replay.json).
The affine job regenerates all twelve least closures; checking the supplied
closures without `--recompute` would establish a narrower result. The
[independent review](data/intake-164-fidelity-review.json) compares the fresh
outputs and recovered bytes. None of these investigations is a premise of the
245-state runtime proof.

Four historical diagnostics also freshly pass in the
[historical replay](data/intake-164-fresh-history-replay.json):

```sh
python3 -B code/state_reduction/safe_lifetime_witness.py --program reference/source/Prog254.v --dag reference/source/Dag254.v --output /tmp/zfc164-lifetime.json
python3 -B code/state_reduction/map_reassociated_leaf.py results/state_reduction/gradient-repaired.json 1110100100101011101010101110000000 --inputs reference/grammar --metadata reference/interval/instruction-metadata.json --output /tmp/zfc164-leaf.json
python3 -B code/state_reduction/check_route_grammar.py results/state_reduction/gradient-repaired.json --inputs reference/grammar --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt --output /tmp/zfc164-seven-zero.json
python3 -B code/state_reduction/check_route_grammar.py results/state_reduction/gradient-zero6-k129.json --inputs reference/grammar --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt --output /tmp/zfc164-six-zero.json
```

These establish the stated safe-root witness, exact ordered leaf mapping and
abstract grammar properties. They do not certify the rejected seven-zero
machine. The time-bounded discovery campaigns and the two bounded pair-merge
searches were not rerun; their delivered outcomes remain historical. No global
minimality result, stronger-theory shortcut, exact 245-state Lean endpoint or
internal PA consistency theorem follows from these executions.
