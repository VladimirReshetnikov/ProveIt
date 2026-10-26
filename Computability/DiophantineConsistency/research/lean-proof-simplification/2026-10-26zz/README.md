# ProveIt Lean simplification seventh review

**One optional local proof cleanup: 10 physical lines removed. Uncompiled.**

Read `report/proof_simplification_report.pdf`; editable TeX and `report/build.sh` accompany it. The exact proposal replaces the new outer seed's local `hKr` power-bound derivation with the already imported `Diophantine.lt_yn_of_two_le`. The entire module changes from 279 to 269 lines. Public statements, definitions, imports and all other bytes remain unchanged. No new mathematical result or broader Pell refactoring is credited.

Source pin: `7ba7d102822df1eff376cbca913727d9d588ab4e` (26 October 2026, 19:25:35 UTC). One closing exclusion screen: `3b51c69d42ff99bc420698532af3fe1d1f9bd356` (19:32:32 UTC). The target remains identical. All six previous deliveries and every prior advertised mechanism, optional branch and real-client adapter are assumed applied, whether merged or not. Fixed-index Pell anchoring, logical dualization, sparse lookup/coefficient bounds and the other advertised controller/arithmetic directions are excluded.

## Contents

- `research/outer_seed/`: exact full-file candidate, patch, metrics, guarded source/finite-arithmetic checker and receipt.
- `research/residual/`: bounded negative search with exact old-mechanism receipts; no promoted patch.
- `sources/`: all 724 active Lean files plus eight context/configuration files. This is not a complete Lake checkout.
- `dependencies/`: 29 selected repository dependencies, including the strict Pell helper and its import route; not a complete transitive closure.
- `provenance/`: complete-tree/hash/history receipts, 19 exact old comparison files via the sibling directory, 20 repository review documents, portable source verification and negative controls. Historical compiler reports are not new compilation results.
- `baseline_audit/`: exact inherited identities, complete new-manuscript semantic review, prior mechanism ledger, closing screen and byte-replay limitations. Raw incoming ZIP bytes and bulk historical source copies are omitted from this small archive.
- `independent_review/`: separate source/guard/import and novelty review, replay and tamper controls.
- `validation/`: replay instructions and portable sealed-archive validation script.

## Minimal replay

Run from the extracted packet root:

```sh
python3 verify_bundle.py --strict
python3 provenance/verify_snapshot.py
python3 baseline_audit/verify_audit.py
python3 research/outer_seed/check_candidate.py
python3 independent_review/check_lemma_reuse.py
bash report/build.sh
```

Use `python3 -O` in place of `python3` to repeat the source/arithmetic checks with Python assertions optimized away; validation uses explicit guards. The PDF rebuild creates files, so strict integrity checks should run before building or against a separate untouched extraction.

To replay an intact ZIP, including an isolated report rebuild and negative integrity controls:

```sh
python3 validation/replay_archive.py /path/to/ProveIt_Lean_Simplification_Round7_2026-10-26.zip
```

This requires Python 3 with PyMuPDF, XeLaTeX and the report's installed fonts/packages. It does not install tools, run Lean, contact the network or mutate an upstream repository. Report and integrity scaffolding is adapted from round 6; it receives no research credit.

## Validation boundary and integration

No Lean or Lake is available in this environment, and neither was installed. All candidates remain uncompiled. Source hashes, 1,953 bounded Pell recurrence samples and three negative domains are not kernel verification. Before adoption, use a complete authorized checkout at the source pin, compile the changed module and existing Checks file and affected reverse dependencies, then compare endpoint axiom reports. No timing or full-project-build improvement is claimed. No upstream changes were made.
