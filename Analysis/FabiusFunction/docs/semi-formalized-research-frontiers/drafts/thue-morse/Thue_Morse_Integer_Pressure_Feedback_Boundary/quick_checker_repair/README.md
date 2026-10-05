# Thue Morse quick checker correction

This separate repair fixes an acceptance bug in the previously delivered first-feedback boundary quick checker. The original checker could exit successfully when traces were missing, and Python optimization could remove its assertions. The original sealed reports, source code, certificates and ten companion archives have not been changed.

The four repaired quick scripts now use explicit exceptions for all 26 former assertions. The trace checker requires the complete original certificate set, checks every input against the original SHA256 manifest, and requires exactly 68 traces and 4828 response orders. Missing, corrupt or mathematically rejected inputs produce a nonzero exit and a failure record. The runner prints its success message only after every child succeeds, preserving the selected optimization level.

## Run against recovered or existing original data

Python 3.11 or newer and its standard library suffice. From this repair directory:

    python code/run_all.py --data-dir /path/to/ProveIt_Thue_Morse_First_Feedback_Boundary/data

Optimization is also safe:

    python -O code/run_all.py --data-dir /path/to/ProveIt_Thue_Morse_First_Feedback_Boundary/data
    PYTHONOPTIMIZE=1 python code/run_all.py --data-dir /path/to/ProveIt_Thue_Morse_First_Feedback_Boundary/data

The data directory is read-only input. New reports go to this repair's results/ directory by default; --output-dir can choose another directory outside the input data tree. The repair deliberately ships no large dataset. A missing default data/ directory fails; there is no partial-success mode.

## Recover the original companion files

recovery/RECOVERY_MAP.md lists all ten existing companion ZIPs, their SHA256 hashes, byte counts, precise moment coverage and extraction destinations. recovery/recovery_map.json gives every member's hash and source comparison. Five boundary trace parts cover all 68 required traces; five separate all-orders interval parts cover 110 interval JSON files. Every one of the 178 entries was compared byte-for-byte with existing local source data and against its original manifest. Nothing was regenerated.

The five boundary parts belong beside the original ProveIt_Thue_Morse_Boundary_Source.zip. The all-orders interval parts belong with ProveIt_Thue_Morse_All_Integer_Orders.zip. The latter files are reconciled for recovery but are not inputs to this boundary checker.

## Regression evidence

    python -O tests/test_fail_closed.py --data-dir /path/to/original/data

The test uses disposable fixtures and checks normal Python, python -O and PYTHONOPTIMIZE=1. It tests complete data, one missing trace, all missing traces, corrupt JSON, corrupt compressed trace, and an injected false mathematical acceptance test in each of the four scripts. It checks exit codes and failure flags, compares the three exact analytic output certificates with their originals, and hashes the sealed inputs before and after. Results are in results/failure_injection_results.json.

source_changes.json records the four original script hashes and assertion counts. source_diff.patch shows the copied-script changes. input_manifest.json is derived from the preserved original boundary manifest; it must remain part of the repair.

## Scope

This is a fail-closed quick-validator repair. Its exact inequalities, baseline vectors, scalar error recurrences, final enclosures and cubic identities are unchanged. Integrity hashes additionally reject changes anywhere in the sealed traces. The quick validator does not recompute every matrix inverse or per-coordinate rounding operation; those belong to the original separate full matrix replay. That optional replay and exploratory scripts are outside this bounded repair and were not modified. The mathematical report's claims are unchanged; no new data or proof certificates were generated.
