# Removing proof layers from K215

Follow-up research, 21 October 2026. This is a separate packet; the previous reports remain unchanged.

Main result: the two actual pinned source decoder trees normalize to identical 1,426-vertex, 2,850-edge increment-weighted test graphs. All 2,240 old correspondence pairs identify the same ordinal on both sides; 814 are aliases. A generic normalization-aware bisimulation theorem could eliminate the explicit correspondence data. The supplied canonical certificate DOES NOT pass the unchanged raw-pointer branch checker. All formalization proposals remain uncompiled.

The logical-calibration patch replaces two unnecessary syntactic round-trip inductions with the existing semantic round-trip theorem. Its net 25-line reduction is a source comparison, not a compiled proof-size or speed measurement. Startup compresses 95,714 transitions into 39,889 independently checked sweeps/single steps; this is not a claimed compiler-time saving. No new Turing machine or 214-state construction is claimed.

## Portable replay

Use Python 3 with assertions enabled and a fresh external directory:

    python -I -B verify.py --work /tmp/layer-check

The script copies owned audit programs and pinned data into that directory before regenerating outputs. It never modifies the frozen packet, executes received Lean code or accesses the network. It parses Lean literals as data; all proof-assistant code is an uncompiled proposal/reference. Results are independent Python checks, not kernel certification.

Structural source pins include Git blob identities at c9dc79323429112c698100f3226a6e4d56c8b782. The corrected increment helper uses exact incRev wrap semantics, including empty to empty; it is tested against an independent recursive transcription on all 2,047 bit strings of lengths 0 through 10. The complete graph equality and raw-pointer audit are rerun afterward. No obsolete overflow helper is packaged.

startup/audit_startup.py is the owned generator and independent finite-support verifier, adapted only to find its two pinned input files within startup/upstream. Its list-zipper generator and absolute-coordinate verifier are separate implementations. Structural scripts are owned independent parsers/checkers. calculus/MANIFEST.json pins the reviewed source files and proposed patch.

Build report.tex with pdflatex twice using geometry, lmodern, amsmath, amssymb, booktabs and hyperref. The delivered PDF is rendered and visually checked separately. The packet contains mathematical designs and proof boundaries, not executable Lean/Rocq certification commands or a complete project checkout.

## Current upstream reconciliation

Main at 05d063acef885d47be5a2ce6645b046f98f7ea02 already adopts the earlier symmetry refactor with recorded kernel checks. This packet does not claim that earlier proposal is still unimplemented. The new graph/decoder/model opportunities remain separate; exact source declarations are independently compared against the pinned c9 snapshot by verify.py. Recorded upstream build logs are not a local rerun. See current_upstream/RESULT.md and REFRESH_RECEIPT.json.

## Exact runtime baseline

The report uses K215_Formal, native SHA 9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2, independently aligned to all 430 literal KTable215 rows and the full formal source tree. The older runtime/K215 label is retained only as separately pinned historical variant evidence. Both have independently measured identical summary counts; no identity is inferred from those counts. The verifier checks all four decoder products, direct and dense formal-table alignments, exact source alignment, and malformed-certificate rejection. Normalization_calls in the historical JSON schema means normalizing endpoint checks, not individual norm-function invocations.
