EVIDENCE GUIDE

reproduction.json is the receipt from the integrated package's reproduce.py.
It records all ten complete-module measurements, 956 isolated executions,
92 recodings, and the exact runtime. verification_summary.json is its compact
summary. expected_metrics.json pins the measured values for CPython 3.12.14.

baseline_census.json records the full pinned source census; baseline_audit.txt
explains eligibility and the incumbent classes. The portable audit script
reproduced the parsed census JSON exactly.

The remaining proof notes and receipts preserve independent reviews of the
component refinements. Some retain their original working filenames:

  tokens242.py                   -> ../code/checker_tokens.py
  bytes_any.py                   -> ../code/checker_bytes.py
  uniform_zero_supply.py         -> ../code/checker_strict.py
  uniform_zero_native.py         -> ../code/checker_native.py
  uniform_zero_native_portable.py -> ../code/checker_native_portable.py
  control616.py                  -> ../controls/strict616.py
  control594.py                  -> ../controls/native594.py

The code contents are unchanged from those audited files. Absolute working
paths in an independent receipt document provenance; they are not runtime
dependencies. The final report and root README give the integrated paths and
the precise contracts. No measured checker imports an evidence file.

uniform_zero_proof.txt contains the corrected universal raw-case soundness
argument and canonical compiler. It covers empty goals and neutral surplus
matrix arities as well as meaningful canonical formulas. Finite test receipts
supplement these proofs; they do not replace them.
