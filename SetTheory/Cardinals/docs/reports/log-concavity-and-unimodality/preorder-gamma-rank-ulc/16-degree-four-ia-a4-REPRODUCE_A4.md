# Reproduction sequence for the independent a4 audit

Use Python 3.11+ (standard library only for a4 checkers), and a C++17 compiler in full mode. Set `PYTHONINTMAXSTRDIGITS=0` and `set -euo pipefail`. Here D is the producer four-attachment directory and A is this independent-audit directory. Relocated copies may change only the `/workspace/shared` path prefix. Preserve source JSON/JSONL bytes; do not rewrite source files just to update paths. Exact certificate lists must come from approved immutable receipts, not a wildcard including still-running searches.

## Full mode, additional first stage

```
python "$A/prepare.py"
g++ -std=c++17 -O2 "$A/recount.cpp" -o "$A/recount"
"$A/recount" "$A/representatives.txt"
```

The recount must exit successfully and print its final PASS. It independently reconstructs all labeled core preorders, all signs and legal types, structural pruning, canonical templates, all Hall support coefficients and exact binomial Newton gaps. `prepare.py` itself only validates schema and creates the interchange text; running it alone is not a kernel audit. `kernel_audit.json` is the immutable audit pin used by later checkers; its input hashes remain valid in the relocated package.

## Both modes

1. Run `python "$A/audit_face_orbits.py"`. This independently rechecks every symmetry action, all zero/positive faces, pruning and the exact remaining face-task ledger.
2. Run `python "$A/audit_global_binomial_squares.py"` followed by the explicit list of every selected approved whole-gap certificate. Each template/gap pair must appear only once per call. Save the resulting `global_binomial_square_audit.json` immediately as a fresh `global_gap_full_replay_receipt.json`.
3. Run `python "$A/audit_global_core_correction.py"` followed by the explicit selected correction-E certificate files. Save `global_core_correction_audit.json` as `global_gap3_coreE_replay_receipt.json`. This checks fresh gamma-to-E reconstruction, the full last-gap decomposition and the exact square identity. It requires the approved exterior-only ordinary lemma and its receipt in the producer directory's parent.
4. Run `python "$A/audit_small_faces.py" --certificates "$D/small-faces/certificates.jsonl"`. This reconstructs all 303 required source targets and their scale/permutation aliases before replaying the identities.
5. Run `python "$A/audit_population_batch.py" --batch "$D/medium-faces" --name medium_checkpoint2 --certificates "$D/medium-faces/certificates_checkpoint2.jsonl" --approved-global-receipt "$A/global_gap_full_replay_receipt.json"`. The fresh global receipt removes the absent template2 middle-gap target. Its input path keys must reflect the relocated files, which is automatic if it was freshly produced by step2.
6. Run `python "$A/audit_core_correction.py"` for template9's nonnegative-binomial E identity, with `core_corrections.jsonl` present.
7. Include the independently audited ordinary proofs and receipts for balanced template34, outward-star templates1/4/10, and the exterior-only lemma. Their mathematical theorems are dependencies, not conclusions of the certificate replay. Verify their recorded source hashes. Template9 combines step6 with the exterior lemma.
8. Run `python "$A/refresh_progress.py"`. For a clean replay, expose only receipts actually regenerated in this run, plus the ordinary-proof approval ledger. Do not let historical receipts stand in for an omitted replay. Assert the desired complete-template set and zero remaining tasks only once every final input is independently approved.

## Additional source dependencies

Besides the kernel, face and certificate JSON/JSONL, `prepare.py` hashes `generate_templates.py`, `polynomials.cpp` and `templates.tsv`; keep them unchanged even though it does not execute the producer generators. The face checker reads `face_orbit_summary.json`. Batch checkers need `selection.json`, `source_faces.jsonl`, `normalized_faces.jsonl`, `face_aliases.json` and the selected immutable certificates in both batch directories. The generic batch checker reads and hashes its supplied freshly generated global receipt and all files listed therein. The correction checker reads and pins `../EXTERIOR_LORENTZIAN_LEMMA.md` and its receipt. Template9's separate correction replay reads `core_corrections.jsonl`.

The independent proof receipts, all immutable approved certificate paths/hashes, and the per-template coverage union are retained in `global_gap*_receipt.json`, `ordinary_global_gap_approvals.json`, and `incremental_progress.json`. These are an approval record; an execution wrapper should report explicitly whether it replayed each certificate or merely checked its immutable hash.
