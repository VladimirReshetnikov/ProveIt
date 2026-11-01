# Pending six-drift replay comparison

These independently reviewed scripts are a template, **not a completed
comparison**. Copy `compare.py` and `run.py` to a fresh evidence directory for
each comparison. Once both 107-module Lean replays have passed, invoke `run.py`
with the frozen plan directory, author directory, peer directory, and optionally
an expected receipt. The wrapper records its comparator subprocess's exit; its
own tool-session exit must be observed separately.

The comparator checks distinct replay states, both full inventories, source and
direct-input hashes, logs and allowed warning classifications, inherited parent
and package companion gates, and both endpoint axiom reports. Its workspace
observation covers 1,104 paths. A source-current flag requires no drift at the
start and end of either child replay and at both fresh final comparison scans;
these are point-in-time observations. The six-drift parent is reconciled by the
guarded rebuild, so the older parent comparator's historical-source flag is not
itself a reason to mark the successor historical. The 848-project ancestor is
still author-only, and package-transitive and dynamic ancestry remain inherited.

`comparator-negative-checks.json` records six fail-closed probes with both
scripts present: missing plan, identical directory, and hardlinked state file,
for each script. These probes are not a positive comparison or Lean replay.
