# Validation support — reused, not a new proof-simplification recommendation

**All supplied Lean candidates are uncompiled.** No Lean/Lake runtime was available, and none was installed. A successful source check is not proof checking.

## What was actually checked

- All **826 selected source files** match their recorded pinned Git-blob SHA-1 and SHA-256 before and after checking. The separately supplied `MRDPCore` dependency also matches its pinned Git blob and SHA-256.
- The annotated and CRT patches pass `git apply --check`, then apply successfully **only inside a temporary disposable source copy**. The supplied `sources/` snapshot was not edited.
- Five candidate artifacts expose **21 explicit fully qualified `#print axioms` targets**. Every public theorem in the selected probes has an audit target. Imports and replay order are explicit.
- The source-plan lexical gate finds no `sorry`/`admit`, new axiom declaration, native reflection tactic/symbol or unsafe/external marker in these candidates. This is not a transitive axiom inspection.
- **33 Python helper tests passed**, including negative tests for empty and missing audit outputs, forbidden axioms, malformed output, compiler errors, unqualified/missing targets, omitted public-theorem audits, source path escape, wrong pins, duplicate outputs and bad prerequisite order.
- Shell syntax passed; the replay harness refused missing direct Lean/Lake binaries with exit 69, without installing anything.

Evidence: `source_validation.json`, `validation_status.json`, `helper_test_output.txt`, `unavailable_preflight.txt`.

## Reproduce the offline checks

From the bundle root:

```sh
python3 provenance/verify_snapshot.py
python3 validation/source_validate.py --json validation/source_validation.json
python3 -m unittest discover -s validation -p 'test_*.py' -v
bash -n validation/replay_candidates.sh
```

`source_validate.py` hashes source bytes and checks all supplied `.patch` files in a temporary copy; it never runs Lean or submitted repository generators. It removes the temporary copy afterward and records target hashes. Its line counts are physical diff additions/removals, **not** the report's full-declaration savings: unchanged context is not counted as a diff line.

## Future Lean replay — not run here

A complete pinned checkout is required. This selected-source archive is **not a standalone Lake workspace**: some local library dependencies are intentionally absent. Use an existing full checkout with dependencies and the required baseline imports already built, and an existing direct Lean 4.32.0 toolchain directory (not elan shims). Use a disposable checkout, since Lake may initialize its own local metadata.

```sh
bash validation/replay_candidates.sh \
  /absolute/path/to/full-clean-disposable-ProveIt-checkout \
  /absolute/path/to/existing/lean-4.32.0/bin \
  /absolute/path/to/new-external-results
```

The harness checks the pinned HEAD, clean tracked sources, toolchain version, locked package directories and prebuilt direct import `.olean` files. It calls neither installers nor `lake build`/update/cache/fetch. `lake env` supplies the existing dependency search path; generated candidate sources, `.olean` outputs and logs go into separate output worlds. In particular, the complete CRT replacement cannot shadow the baseline CRT module in the depth probe. The immutable explicit `replay_plan.json` governs order and expected names; declared candidate prerequisites must precede a consumer and share its output world. Currently the five probes are independent and have no cross-probe dependencies.

Every compiler exit code and raw log is retained. The configuration and direct baseline import object hashes are also recorded; their presence does not authenticate a clean baseline build, which remains an explicit prerequisite. The axiom gate accepts only `propext`, `Classical.choice`, and `Quot.sound`; missing output or any other axiom fails closed. Empty lists/plans cannot pass. Standard axioms are an allowed policy, **not** a statement that all three are used. `check_axiom_log.py` validates supplied text only: it cannot authenticate a log or establish that Lean ran. A legitimate replay also requires the retained compiler exit status, versions, commit and source hashes.

Even a future successful candidate replay is **not a full integration build**. It does not validate C3's proposed helper relocation/compatibility alias or C4's source declaration reordering, nor all downstream uses. Those require a separately reviewed implementation, project build, endpoint audits and relevant Checks modules in the repository's environment. No performance claim is supported.

## Provenance of the support

`static_audit.py`, `check_axiom_log.py`, and `test_tools.py` are copied unchanged from the previous review's validation support. The replay shell script adapts its isolation and explicit-output design; `plan_tools.py`, `test_plan_tools.py`, and `source_validate.py` specialize the support to this new pin and proposal selection. These are reusable review tooling, not repeated recommendations from an incoming manuscript.
