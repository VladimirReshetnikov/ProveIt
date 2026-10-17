# Additional experiments on the actual public 253-state machine

**No smaller consistency machine was obtained.** This contribution searches a new restricted family of two-state fusions, completing the previously unrun local-window check on the public 253-state table and distinguishing failures of a finite checker from semantic impossibility.

## Results

| Experiment | Candidates | Result |
| --- | ---: | --- |
| Pure folds, radius 4 and 64 local steps per side | 63,756 | No sufficient certificate |
| Pure folds, radius 6 and 128 local steps per side | 63,756 | No sufficient certificate |
| Mixed read-row fusions, radius 6 and 128 local steps per side | 50,086 | No sufficient certificate |
| Same mixed fusions, existing affine instruction checker | 50,086 | No full runtime survivor |

The public table is pinned by SHA-256 `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`. Machine-related ProveIt files are frozen at commit `6ec2e80dbbe45a99b7812fb5757977307959a51e`. Full source paths, URLs, and hashes are in `source_manifest.json`.

For mixed fusion, one read action is inherited from each of two parent states; the deleted state's incoming targets and start label are redirected. The family preserves all 55 protected register-box rows after all rewrites and keeps dispatch label 96. Its 25,424 parent pairs generate 50,848 nominal mixed options; 526 are pure or duplicate, and 236 violate the protected-row condition, leaving exactly 50,086.

The affine experiment executes 489,647 affected instruction cases. Its first failures are 45,443 fuel limits, 2,178 unsupported box accesses, 2,259 unsupported symbolic-run operations, and 206 unexpected halts. Fuel limits remain unresolved. Neither this result nor failure of the independent local-window certificate is a lower bound on arbitrary equivalent machines.

`machine_experiments.tex` supplies the full definition, ordinary proof of the local sufficient criterion, scope qualifications, control examples, and numerical tables for inclusion in the report. Both parent states must satisfy the local criterion. A deliberate shortcut checking only the deleted parent is rejected using a machine that scans a blank tape forever before mutation and halts on the first step after mutation.

## Reproduce

Only Python's standard library is required. The supplied input snapshots are immutable and verified against the source manifest before replay. Run without `-O` or `-OO`.

```sh
python reproduce.py
```

The full run takes approximately four minutes in the recorded environment. The following runs the local searches and controls without repeating the affine family search:

```sh
python reproduce.py --quick
```

Inputs may instead be restaged from a local checkout of ProveIt, provided it still contains the pinned source snapshots:

```sh
python reproduce.py --repo /path/to/ProveIt
```

`summary.json` contains compact evidence. Complete per-candidate reports are supplied as `hybrid-fusion-results.json.gz` and `hybrid-window-results.json.gz`; decompress them with any gzip reader. Reproduction emits ordinary JSON files in this directory. A separate `check_controls.py` reproduces the already known runtime-only fold 5→64: all 8,391 affine cases pass, while the exact public bootstrap frame is not reached during two million blank steps. It is an acceptance control, not a new result.

## Attribution and proof boundary

Mira-Cult designed the original machine; mira-emmy supplied the attributed public 253-state reduction; Jeff supplied the verification snapshot and affine design model; Andrew James Wade supplied the underlying TMBuilder framework. ProveIt's source04 and source20 work supplied helper functions, the state-label correspondence, and the protected box boundary. The new search scripts and the mixed-fusion certificate argument are this report's contribution.

The snapshots retain their source text. `LICENSE-ProveIt` records ProveIt's MIT No Attribution license. The ordinary proof establishes why an accepted local certificate is sufficient; the Python checker itself is not kernel verified. The affine executor reuses existing box summaries. The code does not supply a new arbitrary-runtime simulation, a theory calibration, or a proof that a 252-state blank machine has nonhalting equivalent to Con(ZFC).
