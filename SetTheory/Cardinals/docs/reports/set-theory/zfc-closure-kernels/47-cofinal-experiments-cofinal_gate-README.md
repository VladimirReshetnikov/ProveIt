# Cofinal controls: explicit scope

These are complete emitted binary tables for a source/compiler experiment.
They are **not calibrated ZFC consistency machines**.

The final recorded source uses `a+b+d+1` for the general bundle and
`a+b+d+2` for fixed C/G labels 0 and 1. The latter increment corrects a
low-input binder collision in an earlier, superseded `+1` experiment.

| Directory | Working states | Status |
| --- | ---: | --- |
| `original/` | 281 | Unchanged source/compiler control. |
| `cofinal_general/unshared/` | 287 | Unshared modified control. |
| `cofinal_general/best/` | 279 | Best of 32 recorded sharing seeds. |
| `cofinal_fixed_cg/unshared/` | 307 | Corrected fixed-role control. |
| `cofinal_fixed_cg/best/` | 286 | Best corrected control of 32 sharing seeds. |

Each directory includes `machine.tm`, `dag.json`, and `labels.json`.
`results.json` gives all state decompositions, seeds, hashes, and source checks.

Both modified lanes restrict atomic vacuity. The report's counterinterpretation
shows why the ordinary padding theorem is insufficient to calibrate that
logical engine. Every table also inherits an unproved changed-startup
invariant and a missing framework row totalized to halt without an
unreachability proof. State savings against the281 control do not transfer
arithmetically to the optimized252 reference.
