> FINAL NOVELTY OVERRIDE: H1/H2/B1 are superseded comparison evidence, not new proposals. See `../late_review/` and the final report. This original source-only review does not incorporate the late novelty screen.

# Independent validation — fourth review

**Passed: source-only checks. All proposed Lean is uncompiled.** There were no Lean/Lake invocations, runtime installations, upstream edits, actual axiom outputs, project build, or runtime measurements.

From the artifact root:

```sh
python3 validation/source_validate.py --json validation/source_validation.json
python3 -m unittest discover -s validation -p 'test_*.py' -v
python3 helical/validation/test_candidates.py
python3 bridges/validate_static.py
bash -n validation/replay_candidates.sh
```

`source_validate.py` checks 914 source, 6 separate dependency, and 11 historical comparison hashes; active coverage/delta; all four patches in a disposable source copy; exact equality with five complete proposed modules; preservation of original declarations/imports; pinned Mathlib evidence; exact audit suffixes; and reproduction of 21 outputs by three supplied generators in a disposable copy. It never runs Lean. Original source bytes are rechecked afterward.

The independent suite has **60 tests**, including negative controls for manifest corruption, missing or empty axiom outputs, native/sorry axiom reports, missing/undeclared/reordered overlay prerequisites, absent toolchains, elan shims, an unsafe selected-source checkout, signed transport, excluded right wall, and invalid small heights. The separate author suite has 10 tests. The bridge author static/model report is also rerun. These counts do not measure mathematical proof coverage.

## Future authorized replay (not executed here)

```sh
bash validation/replay_candidates.sh \
  /absolute/full-pinned-disposable-checkout \
  /absolute/existing-direct-toolchain/bin \
  /absolute/new-external-output-directory
```

The checkout must be clean and pinned to `e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`, with existing Lean/Lake 4.32.0 binaries, its locked package directories, and prebuilt unaffected import modules. The script does not install, fetch, update, or run `lake build`. Future `lake env` may read/init local metadata, hence the disposable-checkout requirement. Early refusal paths alone were exercised now; `unavailable_preflight.txt` records exit 69 before any runtime invocation.

Nine modules use one output world, in this order:

1. **changed** FinishConstruction
2. **changed** TraceCycle
3. unchanged CycleBoundary
4. unchanged CycleMarker
5. **changed** HelicalQuotient
6. unchanged HelicalExtension
7. **changed** CycleBand
8. unchanged HelicalMarker
9. **changed** BandMarker

All names have the prefix `DiophantineConsistency.WangTiles942`. Rebuilding the four unchanged connectors prevents a new consumer from depending on a stale prebuilt intermediary. Direct overlay imports are validated against their declared earlier prerequisites. In particular, BandMarker cannot be checked against old CycleBand, and CycleBand cannot indirectly reach old HelicalQuotient.

`replay/*.lean` consists of the exact measured candidate (or unchanged connector) plus an appended fully qualified `#print axioms` block, outside every size metric. `replay_plan.json` lists **96 public theorem targets**, including every public changed/new theorem. The private halted helper is covered transitively by both public callers. No private compiler name is guessed.

The future log gate rejects missing endpoints, empty endpoint sets, malformed axiom lines, compiler errors, `sorryAx`, and unknown/native axiom names. It admits only `propext`, `Classical.choice`, and `Quot.sound`. A hypothetical pass would certify selected candidate elaboration/axiom output only—not a complete project build or an all-prior-proposals-applied integration tree.

Support adapted from round three is identified in `reused_support_manifest.json`; validation infrastructure is not credited as another simplification. `INDEPENDENT_REVIEW.md` gives the mathematical and novelty review. `validation_status.json` records the observed boundary.
