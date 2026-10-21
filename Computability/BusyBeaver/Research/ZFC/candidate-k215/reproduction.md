# Reproduction and evidence scope

The main machine is reconstructible without numerical optimization. The exact accepted216 source/table inputs are retained under `code/source-inputs/partial216`; an external parent can also be selected with `--parent`:

```sh
python3 -B reconstruct.py --out /fresh/k215-rebuilt
python3 -B code/check_source.py --out /fresh/k215-source-review.json
```

This rebuilds the exact 4,751 source rows, native215 table, and dense215 table from the parent source/table and the two literal recipes. It checks their pinned bytes and the complete reversible native/dense state map.

The inherited native-label runtime leaf is retained with its exact import closure. From this directory, use a fresh output:

```sh
python3 -B code/fresh_check.py --out /fresh/k215-runtime-run
```

This standard-library wrapper checks eight frozen input pins, creates a fresh output directory, checks the calibrated blank frame within 500,000 transitions, and gives the copied runtime leaf one 360-second process cap. It preserves any failure and raw output. Its success gate requires the complete runtime result; the underlying leaf's process return code alone is insufficient. Require `runtime.json` status `UNIVERSAL_MATHEMATICAL_PASS`, exactly 6,176 expected and proved cases,215 working states, no failures, unchanged input hashes, and the complete ordered case records. The leaf also emits the blank startup trace and complete terminal frame. An independent startup/record audit remains separate from that leaf. Root's fresh invocation uses a 360-second process cap; the checker uses its unchanged symbolic-case bound. These are execution bounds for constructing and checking the finite certificates, not bounds on the natural register values represented by the proofs.

Root's original absolute-path runner is retained unchanged at [evidence/root-runner.py](evidence/root-runner.py). Its actual fresh run passed all 6,176 cases, with 1,698,790 symbolic rules and all 430 rows covered. The native and dense blank traces independently replay to the exact frame after 95,714 transitions, with native dispatcher 84, head −8, gap 1, registers `[4,0,0,0,0,0,0,0,0]`,40 unit spares and 95 one cells.

To expand the exact archived root run and invoke the unchanged independent saved-record/blank auditor without rerunning the symbolic proof:

```sh
python3 -B code/prepare_actual_view.py --out /fresh/k215-archived-view
python3 -B reviews/review_actual.py --run /fresh/k215-archived-view --output /fresh/k215-actual-review.json
```

The view preparation verifies every raw and stored hash, restores compressed JSON byte for byte, and copies the same eight frozen inputs. The independent auditor checks every saved case and row and independently replays both finite blank traces; it imports no supplied checker. Large case/startup JSON files are archived with deterministicgzip and an exact raw-byte index. The portable source/reconstruction and view-preparation utilities have been checked on fresh paths. The fresh-runtime wrapper is a reviewed relocation of the actual root invocation; the original full run is the accepted execution, and a second full run has not been claimed.

The research directory preserves the actual source composition, exact parser utilities, bounded allocator, initial global-alias rejection, separate corrected local-entry audit, dependency-install failure, identity control, solver environment and independent prospective review. Those original exploratory scripts retain their original paths and logs. Their source/DAG cost is evidence about this particular construction, not an exhaustive optimum. Re-running the solver is unnecessary for table reconstruction or verification.

The inherited logical certificate, predecessor suites, archive manifest wrappers and proof-assistant builds are not replayed by these commands. The ordinary proof links the exact newly checked source to the separately reviewed dominated calculus and command compiler. No new exact 215 Lean/Rocq or PA endpoint is claimed.
