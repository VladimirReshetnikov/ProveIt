# Decoder coverage for the exact 240-state machine

The [complete direct240 coverage proof](rotation240_coverage_complete.md)
checks all 530 subtrees and 529 structural joins over 6,455 leaves and 8,386
guarded cases. Its 565 modules pass 1,062 named probes and 1,066 typed callers
with zero warnings, establishing `SitesRotation240.all_sites`. The
[external binary endpoint](rotation240_binary.md) now combines that theorem
with the runtime, blank startup frame and register-source calibration.
The internal PA equivalence remains a separate obligation.

The [archived history and reconstruction instructions](rotation240-coverage/publications/complete/README.md) preserve the complete proof and review records.

## Historical checkpoint: 132 cuts and the first 16 joins

The following text and linked records describe the earlier partial
publication. Its pending-status statements are historical; the records and
archived proof attempts remain unchanged.

The current Lean coverage proof is **partial: 132 of 530 subtrees have passed**.
These disjoint subtrees contain 1,568 of 6,455 leaves and 2,045 of 8,386 guarded
instruction cases. The four initial pilot proofs and first 128 production
proofs passed 132 theorem probes and 136 typed callers, with zero warnings.
The complete `all_sites` theorem has not yet been checked.

The [first structural join module](rotation240_coverage_join000.md) has also
passed 16 probes and 16 typed callers with zero warnings. It combines already
checked subtrees, so it adds no leaf or guarded instruction cases. The current
cut and first join packets together account for 148 probes and 152 callers.
Other joins and the final `all_sites` theorem remain pending.

Each successful theorem evaluates `SiteRotation240.checkSite` on the exact
subtree of `TreeRotation240.tree`, retaining the complete root-path prefix.
Both decrement outcomes are included. The four pilots cover a changed
source-loop occurrence, the longest zero run, the deepest frontier path and
the halt case. The remaining changed-loop occurrences are still included
among the pending production obligations.

The complete generated plan has 530 subtrees, 529 binary joins and one final
module. It reuses the four successful pilot modules directly and adds 526
new subtree modules, 34 join modules and the final module. Every join requires
both child proofs. The final theorem must establish coverage for every path
through `SourceRotation240.program`. None of the older 244-state coverage
certificates substitutes for a fresh 240-state check.

The [current cut progress record](results/rotation240-coverage-progress132.json)
identifies every successful cut module. The
[initial progress record](results/rotation240-coverage-progress.json) is retained
unchanged. Successful sources are installed in the Lean tree;
[typed audits](rotation240-coverage/audits/) and the
[first completed batch record](rotation240-coverage/batch000-063.json) are
preserved. The [history archive](rotation240-coverage/initial-progress-history.json.gz)
retains raw actual records and logs, preparations, source-generation code,
the entire generated family, and independent source/guard reviews. Unchecked
generated files in that archive retain their status at the initial checkpoint.
The [second batch record](rotation240-coverage/batch064-127.json) and
[second batch history](rotation240-coverage/batch064-127-history.json.gz)
preserve the next 64 successful source/audit pairs and their preparation and
raw execution evidence. Those pairs took 481.782 seconds for sources and
28.902 seconds for audits in total; each pair had its own shared deadline.
The remaining generated files are proposals, separate from the installed
successful modules.

Every source/audit pair uses one thread, 4,096 MiB, default proof limits and
a shared 120-second deadline. The site-check fuel is 4,000 and the frame
margin is 64. The [original serial guard](rotation240-coverage/check_production.py)
requires actual successful predecessor records, records each fresh object
before auditing it, and checks its exact imports. It retains historical
scratch paths; this publication does not provide a clean-checkout build.

Complete coverage remains necessary to compose the
[general runtime proof](rotation240_runtime.md),
[blank startup frame](rotation240_tree_frame.md), and
[register-source consistency calibration](calibrated_rotation240.md).
The internal PA equivalence remains a separate obligation. Attribution follows
the imported Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt proofs.
