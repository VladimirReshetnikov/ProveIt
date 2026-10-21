# Source157 selected fresh reproduction

The replay consists of six inspected leaf checkers on a fresh disposable copy. It does not run the archive's wrappers, manifest checks, old full runtimes, search programs, proof builders, manuscript build or Coq/Rocq. All dependencies are standard-library Python; the source certificate imports only its included, inspected `source_language.py`.

Recover the complete Source157 archive using the intake recovery procedure. Set `PACKAGE` to the recovered `ZFC_217_Scanner_Source_Research_2026-10-21` directory and `BUNDLE` to this fresh-evidence bundle's `review` directory. The output plan and run directory must be new:

```sh
python3 -B "$BUNDLE/prepare_replay.py" --package "$PACKAGE" --output /tmp/source157-fresh-plan.json
python3 -B "$BUNDLE/run_selected.py" --plan /tmp/source157-fresh-plan.json --output /tmp/source157-fresh-run
```

The preparer binds only selected mathematical code/data identities. The runner copies the package, preserves the original source checker and overwritten copy-side receipts, then applies the exact recorded manifest-loop removal in `source-check-adapter.diff`. All mathematical assertions remain. The original packet is never modified. `code/check_packet.py` retains its four explicit mathematical input-provenance checks.

Each subprocess has an external120-second cap, assertions enabled, raw stdout and stderr, and a recorded command/environment. A nonzero status, timeout or failed semantic gate stops the batch and preserves the failure. No new source/audit limits are substituted. `actual.json` records all before/after selected input hashes. The result is accepted only when status is `PASS_ALL_SIX_SELECTED` and all45 semantic gates have passed.

| Leaf | Required semantic result | Fresh recorded outcome |
|---|---|---|
| Scanner local | Three positive whole-tape blocks, retained two contextual premises | PASS, lengths1/1,2/4,3/3 |
| Literal packet | Exact five table censuses; complete root startup; wrong-return witness | PASS,104082; ordinal40,588 versus662 |
| Restricted-L matrices | Two exact matrices; retained rows/rules and aliases; failed S/K and excluded bundle | PASS,7×27 assignments per matrix, bundle values1/2 |
| Seed reflexivity | Closed derivation of native3, inherited K/S scope | PASS,79 nodes,40MP,1GEN |
| Local-7 source | Exact replacement/wrong-MP tuples and halting suffix | PASS source counterexample, no binary blank-run claim |
| Six source recodings | Complete word/CFG/initializer equality; exact source metrics | PASS,6×6176 no-stray checks; five206-node zero-run5 trees |

The recorded first run used Python3.13.14, zero optimization, and finished all six processes in about1.03 seconds with empty stderr. All fresh result JSON objects equal the delivered corresponding receipts. This equality is a reproduction observation, not a substitute for checking semantic gates. The separate55-check artifact review is recorded in `actual-review.json`; its author also wrote/executed the runner, so it is not labeled a second-agent independent peer.

The source-only dossier, own runner draft that failed AST parsing before execution, original checker, exact adapter diff and delivered receipts overwritten only in the disposable copy are retained under history. No supplied check failed. The all-natural seed theorem and native derivation soundness remain ordinary mathematical review beyond the finite replay. The scanner's non-scanner77/1 obligation, new physical allocation and new whole runtime remain open.
