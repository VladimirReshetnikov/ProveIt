# Decoder coverage for the exact 240-state machine

The current Lean coverage proof is **partial: 68 of 530 subtrees have passed**.
These disjoint subtrees contain 791 of 6,455 leaves and 1,038 of 8,386 guarded
instruction cases. The four initial pilot proofs and first 64 production
proofs passed 68 theorem probes and 72 typed callers, with zero warnings.
The complete `all_sites` theorem has not yet been checked.

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

The [progress record](results/rotation240-coverage-progress.json) identifies
every successful module. Their sources are installed in the Lean tree;
[typed audits](rotation240-coverage/audits/) and the
[first completed batch record](rotation240-coverage/batch000-063.json) are
preserved. The [history archive](rotation240-coverage/initial-progress-history.json.gz)
retains raw actual records and logs, preparations, source-generation code,
the entire generated family, and independent source/guard reviews. Unchecked
generated files in that archive remain proposals, separate from the installed
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
