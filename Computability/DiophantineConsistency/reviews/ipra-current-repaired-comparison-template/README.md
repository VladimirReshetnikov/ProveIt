# Pending current-source comparison

This is a statically reviewed, **unexecuted** comparator and subprocess-exit
recorder for the 258-module replay. It must only be run after both independent
Lean processes have finished successfully. Copy these scripts into a fresh
verification directory for each run; `run.py` takes the frozen plan directory,
author directory, peer directory, and optionally an expected receipt path.
It rejects the same directory or physical state file as both peers, preserves
the comparator log, and records the comparator subprocess exit. The wrapper's
own exit must also be observed separately.

The comparator audits input hashes, original and selected project environments,
external companion presence and absence, all output objects and full logs,
the endpoint axiom reports, and workspace source drift. An empty drift report
at its checks applies only to those observation times. The parent retains its
documented inherited external package-transitive and dynamic-import limits.

The scripts were independently reviewed after the distinct-peer and failure
marker fixes. A focused negative check in
`../ipra-compare-same-run-negative-g_ieo09c/negative-check.json` exercised the
same-run rejection and records an initial wrong-root probe that did not reach the
intended guard. No replay or comparison pass is asserted by this template.
