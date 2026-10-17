# Ready offline batch156 runner (scratch implementation)

`reproduce_156.py` is self-contained and requires only standard-library Python for recovery/default suites. It recovers all three ZIPs from Git arrival `2447a98214b1c4a3e24e51ee654439fbcfa002d9`, so retired incoming archives need not remain in the current checkout. It uses no network or Lean/Coq process. No delivered source file is patched; all suite execution is on recovered scratch copies.

```sh
uv run --no-project python -B /tmp/zfc-intake156/reproduce_156.py --repo /absolute/Proofs --prepare-only --output /new/external/scratch
uv run --no-project python -B /tmp/zfc-intake156/reproduce_156.py --repo /absolute/Proofs --run all --output /different/new/external/scratch
```

The default without `--run` is prepare-only. Outputs must be new or empty and outside the checkout. `recovered-paths.json` records every original delivered path, recovered path and corresponding staged flat path (or `null` for article/PDF/bibliography/top-level README retained in the arrival archive). The 313 reconstructed mappings were compared with the root's placement-map draft: exact, comprising47:163 staged/11 archive-only,48:53/17,49:56/13. This is a path-mapping comparison, not a bulk content-checksum audit.

Manifest handling is intentionally narrow:

- Source47: the in-memory AST adapter replaces exactly one `check_sources` bulk provenance checker and omits exactly six named release-record checksum/byte-count assertions. It fails closed if the expected function/assertion shapes change. It keeps canonical and old table identity guards; all504 Lean table actions; all82,552 bootstrap steps/77 nonzero cells; logical diagnostics; all166,413 delivered journal recipes/order/category/count checks; the strict-affine/Prog254 functional source pins; and all five compiler-table identities/row counts. The default **reads and checks the delivered search journal**, without rerunning the affine search or compiler.
- Source48: the delivered native `--skip-manifest` option is used. All table/source-export identities and functional regeneration checks remain. There is no nested bulk loop in its advertised driver.
- Source49: the delivered `code/verify_bundle.py` is executed directly, with no adapter. The root and nested advertised drivers contain no bulk manifest loop. Actual input-table identity guards remain.

Optional compiler/search re-execution:

```sh
# Source47: all32 seeds in each of the two compiler-control variants.
uv run --no-project python -B /tmp/zfc-intake156/reproduce_156.py --repo /absolute/Proofs --run 47 --compiler-controls --output /new/compiler/scratch
# All selected sources: source47 compiler +166,413 incoming-action recipes;
# source48 both full deletion ledgers +four residue analyses;
# source49 radius-six and radius-eight full fusion ledgers (requires g++).
uv run --no-project python -B /tmp/zfc-intake156/reproduce_156.py --repo /absolute/Proofs --run all --extended --output /new/full/scratch
```

`--extended --run 47` runs just source47's optional jobs. Its search is capped at600 seconds by default; `--search-seconds` changes that budget. A time-limited partial result fails the completed-replay comparison. The source47 compiler comparator requires complete results JSON equality plus15 exact selected table/DAG/label files. The search comparator requires every functional summary field (six explicitly listed environment/timing/journal-location fields excluded) and all166,413 journal rows byte-exact against the decompressed delivered journal. These are functional experiment comparisons, not release-manifest checking.

This helper does not run PDF builds, optional figure rendering, proof assistants, or every ancillary source49 rotation/multi-fusion parameter branch. Source49's `--extended` covers the two full ledgers advertised by its aggregate `--full` driver; separate driver branches are documented in the source49 dossier and root's independent extra-job evidence. A script-level PASS records the requested finite checks only, and does not execute an unbounded consistency proof or establish a new state record.

Prior source47 full compiler and search replays already completed during independent intake review. The new helper's comparison functions were exercised against those outputs with the newly recovered package, and both passed; this does not rerun the full searches a second time. The default all-source helper validation is recorded separately under `/tmp/zfc-intake156-helper-validation/verification.json`.
