# First checked structural joins for direct240 coverage

[`SitesRotation240Join000`](../../Lean/BusyBeaver/ZFC/SitesRotation240Join000.lean)
checks the first 16 structural joins (`join_0` through `join_15`) in the
fresh direct240 decoder-coverage plan. Each join requires both child proofs
and retains the complete root-path prefix. Its 18 imported cut proofs are
already part of the initial checked cuts; these joins add no new checked
leaf or guarded instruction case.

The [actual record](rotation240-coverage/join000/verification.json) passed
16 named probes and 16 typed callers with zero warnings. Source took
1.324 seconds and audit 0.597 seconds, within one shared 120-second deadline,
one thread, 4,096 MiB and default proof limits. The exact prerequisite
closure has 48 project modules plus Init and Omega; the fresh object and
its first provider were captured before the audit.

The [additive progress record](results/rotation240-coverage-join000-progress.json)
links the unchanged initial 68-cut progress record. Together those two
snapshots account for 68 checked cuts, 16 checked joins, 84 probes and
88 typed callers. The cut census remains 791 leaves and 1,038 guarded
cases. This is a partial result: the final `all_sites` theorem has not been
checked, and no binary consistency endpoint or internal PA equivalence
follows from this packet.

The [typed audit](rotation240-coverage/audits/SitesRotation240Join000.lean),
[preparation](rotation240-coverage/join000/preparation.json),
[batch record](rotation240-coverage/join000/batch.json), raw source/audit logs,
[existing-evidence review](rotation240-coverage/join000/actual-review.json), and
[lossless history](rotation240-coverage/join000/history.json.gz) preserve the
successful bytes. The history also retains the immediate-parent records and
the exact common guard/manifest. Compiled caches are excluded. The review
author also authored the coverage generator/guard proposals; root independently
performed the actual execution. Packaging performs no proof replay or dependency
build and retains historical provider paths.

Attribution follows the imported Mira-Cult, Jeff Ketchersid, Andrew James Wade
and ProveIt constructions and the existing direct240 coverage proof pattern.
