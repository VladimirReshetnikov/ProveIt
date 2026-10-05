# Archived numerical diagnostics only

`exact_dp_3000.json` is a legacy filename. Its contents are **high-precision numerical diagnostics**, not an archive of exact integers and not an interval certificate. The original producer constructed integer triangle rows in memory, then retained sampled decimal evaluations at working precision 90. Neither those integer rows nor rigorous rounding/error bounds were archived in this JSON.

`numerical_analysis.json` is a subsequent numerical analysis of those samples. Amplitude extrapolations and any displayed digits are unverified numerical estimates. Neither file is input to the mathematical acceptance tests. Their byte hashes are checked solely for archival integrity.

No n=3000 dynamic program, eigenvalue computation, or amplitude extrapolation is rerun by `verify.py` or `negative_tests.py`. In particular, passing this package does not certify numerical gamma digits, eigenvalue asymptotics, or existence of an amplitude limit. Exact finite checks and analytic proofs have different scopes.
