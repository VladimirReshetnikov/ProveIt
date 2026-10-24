# Independent integer review

Read `INDEPENDENT_REVIEW.md` for the mathematical review and exact degree arguments. `AUDIT_RESULTS.json` is the recorded computational audit, and `PREDECESSOR_BINDINGS.json` authenticates the directly used source notes against the supplied baselines.

Run from any working directory:

    python review/integer/independent_audit.py
    python -O review/integer/independent_audit.py

The script requires only Python's standard library and the adjacent `integer/` package. All exact algebra, literal-core, degree, coefficient, topology, and local source-digest checks are self-contained. If `baseline/ProveIt/.git` is present, it additionally checks every retained ordinary source against the exact pinned Git blob without lazy fetch. If that optional clone is omitted from the delivery, the report explicitly marks those Git comparisons as not rerun. The recorded delivery audit performed them successfully.

The random register evaluations are finite diagnostics. The universal norm/core identities and leading-coefficient calculations are exact polynomial identities. Neither replaces the unbounded mathematical reduction and its named imported ordinary calibration.
