PORTABLE CENSUS REPRODUCTION
===========================

The frozen evidence is census_complete.json / .csv, baseline_fingerprints.json,
baseline_audit_summary.json, and baseline_download_manifest.json.
The manifest names exactly 3,356 repository files (27,179,752 bytes): all
integrated *.py and *.py.gz source files plus the 16 current incoming ZIPs.
Archive contents and compressed source are parsed statically, never executed.

Existing checkout:
  python3 reproduce_census.py --manifest PATH/baseline_download_manifest.json \
    --source-root /path/to/ProveIt --output census-rerun

Or download exactly the required public bytes first:
  python3 download_baseline.py --manifest PATH/baseline_download_manifest.json \
    --destination baseline-source
  python3 reproduce_census.py --manifest PATH/baseline_download_manifest.json \
    --source-root baseline-source --output census-rerun

Use CPython 3.12.14 for the exact normalized-source metrics. All files are
verified against their frozen SHA256 and byte length before parsing. The
manifest also records Git blob SHA1 identities. The measured snapshot is
ProveIt commit 1156099ffe30f7497d2c11ab20271f46cffcd115.

Expected result: 3,601 source occurrences, 1,813 distinct normalized modules,
and zero parse failures. All source rows of census-rerun/census.json should
equal the frozen census_complete.json rows. Descriptive headers can differ.

No automatic filter proves that a program satisfies a particular theorem,
calculus or validation contract. The selected incumbent controls and their
documented input contracts have been reviewed separately. Numerical floors
are empirical source comparisons, not proven lower bounds on all possible
presentations.

Exact normalized-source duplicate checking:
  python3 check_candidate_novelty.py path/to/candidate.py \
    --index PATH/baseline_fingerprints.json --output novelty.json

That check can establish absence of an exact normalized-source duplicate in
the pinned corpus. It cannot establish mathematical novelty.
