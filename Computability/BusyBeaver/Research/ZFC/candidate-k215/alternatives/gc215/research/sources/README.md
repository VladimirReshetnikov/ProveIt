# Exact source-cost artifacts

This directory supplies the representative sources behind the experiment ledger in `research/research_costs.json` and `research/research_costs.md`. All paths in that ledger are relative to the archive root unless explicitly labeled historical.

Run the independent, standard-library cost audit from the archive root:

```sh
python3 research/sources/audit_costs.py
```

The audit recomputes literal source-tree metrics and checks all recorded source and receipt hashes. Its delivered receipt is `cost-audit.json`. It establishes source costs only, not semantic correctness, binary execution, or state-count lower bounds.

The selected GC215 source is in `source/gc215.sites.json`. Sources here include rejected and uncalibrated probes; consult each ledger status before treating one as a candidate. The guardless source cannot halt, and the rotating-pop source is a prior uncalibrated comparator.

`inputs/` contains the two additional source seeds needed to identify these experiments exactly. The immediate ST215 seed is shared with `reference/st215.sites.json`.

`receipts/` preserves original bounded-search, allocation, and experimental metadata verbatim. Their internal workspace paths are historical identifiers. The optimization scripts are not part of the portable replay, and failure to find an allocation is not an impossibility result. The complete representative sources make the recorded costs directly reproducible without rerunning an optimizer.
