# Reused validation support — not a new simplification recommendation

**Every supplied Lean candidate remains uncompiled.** Neither Lean nor Lake is available on this executor; no runtime was installed. Hash checks, finite Python models and textual proof review are not Lean checking.

## Established here

- All **860 selected sources**, and the **5 separately supplied BusyBeaver dependencies**, match their pinned Git blob SHA-1 and SHA-256 before and after checking. There are **608 active DiophantineConsistency Lean files** in the selected snapshot.
- The two required Mathlib source files and bundled license match the locked Mathlib revision and their recorded hashes.
- All **six patches** pass `git apply --check`, then apply together in a temporary disposable source copy. Neither `sources/` nor `dependencies/` is changed.
- Four probe files expose **nine explicit fully qualified `#print axioms` targets**, outside their theorem/namespace spans. Every public candidate theorem is listed; no such command was run.
- The lexical gate finds no `sorry`/`admit`, new axiom declaration, native-reflection tactic/symbol or unsafe/external marker. This is not transitive axiom checking.
- **48 Python tests pass**: 33 reused helper/negative tests, nine bounded semantic-model tests, and six independent source-contract/metric checks. Negative guards include empty/missing audit output, forbidden axioms, malformed output, compiler errors, unqualified/missing targets, omitted public theorem audits, source escape, wrong pins, duplicate outputs and prerequisite order.
- Shell syntax passes. The missing-runtime preflight refuses to proceed with exit **69**, without an installation attempt.

Evidence: `source_validation.json`, `validation_status.json`, `helper_test_output.txt`, `unavailable_preflight.txt`, `INDEPENDENT_REVIEW.md`.

## Offline reproduction

From the bundle root:

```sh
python3 provenance/verify_snapshot.py
python3 validation/source_validate.py --json validation/source_validation.json
python3 -m unittest discover -s validation -p 'test_*.py' -v
bash -n validation/replay_candidates.sh
```

`source_validate.py` hashes bytes, verifies the explicit plan and checks patches only in a disposable copy. It does not run Lean, Lake, repository generators or network requests. Its diff line counts are physical additions/removals, not declaration savings.

The finite models in `test_semantic_models.py` check intended direction/sentinel/boundary conventions and counterexamples. They do not execute Lean definitions, certify tactics, prove unbounded statements or replace existing decoder certificates. Independent source tests verify exact statement headers, unchanged executable definitions, the extra import, audit placement and measured nonblank declaration spans.

## Future Lean replay — not run here

This selected archive is **not a standalone Lake workspace**. Supply a complete, clean, disposable checkout at commit `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`, already built direct imports and locked dependencies, and an existing **direct** Lean 4.32.0 toolchain directory (not elan shims):

```sh
bash validation/replay_candidates.sh \
  /absolute/path/to/full-clean-disposable-ProveIt-checkout \
  /absolute/path/to/existing/lean-4.32.0/bin \
  /absolute/path/to/new-external-results
```

The harness checks HEAD, clean tracked sources, toolchain version, package directories and direct-import `.olean` presence. It invokes no installer, `lake build`, update, cache or fetch. `lake env` supplies existing dependency paths; Lake may initialize local metadata, hence the disposable-checkout requirement. Candidate sources, object files and logs use separate output worlds. The immutable replay plan controls order and expected audit names. All four probes are independent.

Raw logs, compiler exit codes, source/configuration and direct-import object hashes are retained. Prebuilt object presence/hashes do not authenticate a clean baseline build; that remains a prerequisite. The log policy permits only `propext`, `Classical.choice`, and `Quot.sound`, rejects missing output and is not an authenticity check. These are allowed axioms, not a claim that all are used.

A future success would establish only candidate elaboration and selected axiom policy against that exact checkout. It would **not** establish a full integration build or compile the virtual assumed-adopted proposal baseline. The latter is an outcome/API model, not a mutually compatible executable patch union. Integrating all previously adopted proposals, applying the six changes, checking edge-API consumers, running affected original Checks modules and auditing final public endpoints remain separate acceptance gates. No performance result is supported.

## Reuse provenance

`static_audit.py`, `check_axiom_log.py`, `test_tools.py`, and `test_plan_tools.py` are copied unchanged from round two. `plan_tools.py`, `replay_candidates.sh`, and `source_validate.py` adapt that support to this pin/probe selection. `test_source_contracts.py` and `test_semantic_models.py` specialize textual and finite-model checks. See `reused_support_manifest.json`. None is offered as a new proof-simplification idea.
