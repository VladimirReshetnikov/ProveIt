# Mask-cover second retry: scoped prelaunch review

**GO for one coordinated v3 author retry** with source SHA-256 `66991596012af7ec03a3ac082865fe4bbd367205e36ec45d89070f2977d258d2` and runner SHA-256 `9b57e657ab755d73bfdd742b3681b282f92847a46359afb4235272619b1047bf`. No Lean was run in this review.

Retained attempt02 terminal SHA-256 `bafe95dc4b4533cc44f45647795aa6f93c1fe458603c328ad49b96802bf4645b` records failure, with an addition-orientation mismatch and a goal caused by rewriting inside truncated subtraction, followed by `sorryAx`; author reports actual session 60890 exited 1 and was reaped. The source diff against that attempt's snapshot adjusts the additive orientation via `simpa` and uses `congrArg` followed by `ring` to avoid the problematic inner rewrite. The theorem statements and assumptions are unchanged; the runner diff changes only its source pin. Both failed attempts are excluded from acceptance.

Independently reran the read-only source/direct-provider/resource preflight and all 15 actual report-policy controls successfully. The prior scoped prelaunch review's direct-pin and inherited project/package/dynamic ancestry limitations remain. A successful run would prove only the conditional comparison theorem, not any graph-zero hypothesis, fixed-mask binding, full guard or iPRA statement. Actual tool exit and result need a post-audit.
