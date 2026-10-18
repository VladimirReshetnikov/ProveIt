# Whole-tape framing for prefix250

`Prefix250Simulation.lean` connects the checked prefix250 symbolic
representation to the generic dispatch frame. It strips explicit zero
padding without discarding any tape cell, rebases a clean consumed PC,
and reconstructs a complete target frame with the updated register file.

Increment appends a value-one spare. Positive decrement preserves the
spare suffix and adds one to the header distance. The target includes an
explicit additional-distance parameter, independent of PC overflow. The
validity clients require a nonempty spare suffix, so nine primaries always
have at least one following block. Register-update identities themselves
allow arbitrary spare lists.

Root's first source/audit attempt passed: 14 named axiom probes, 14 direct
callers, and only `propext`/`Quot.sound`. Source took 0.974 seconds and audit
0.521 seconds. One unused `List.append_assoc` simp argument warning remains
in the exact successful source; the audit has no warnings. The guard uses
one thread, 4,096 MiB and a shared 120-second wall limit, with default Lean
proof limits. No dependencies were rebuilt.

The exact provider closure contains 21 project modules, supplied through
the checked SitePrefix250 parent and the maintained MP-control evidence.
The three additional modules are RegisterPathClean, RMEquiv and RMDag.
Init and Lean.Elab.Tactic.Omega are explicit supplied toolchain boundaries.
The guard records the fresh source object before compiling the audit and
checks it again afterward. Its published source and audit are the exact
successful bytes; publication changes only the guard's two default paths.

From the repository root, using a new external output directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_prefix250_frame.py \
  --repo "$PWD" \
  --site-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-site-verification.json \
  --output /tmp/zfc-prefix250-frame-check --prepare-only
```

This preparation checks paths, identities and providers without running
Lean or querying its version. Removing `--prepare-only` requests the
bounded source/audit proof check. The original successful record, full
run history and author evidence review are retained under
`results/prefix250-frame-*.json`. Parent histories remain in their own
records. Root independently read the source, audit and guard before the
sole execution.

These are conditional framing adapters. They do not assert acceptance of
any concrete site, complete decoder coverage, a blank bootstrap, an exact
250-state consistency endpoint or PA internalization. Those obligations
remain separate. The layout and framing strategy retain Mira-Cult, Jeff
Ketchersid and Wade's attribution from the maintained permutation252
modules and upstream commit `297ab8df7e5de329605c3875b4934643b371a5e3`.
