# Provisional source-directed 14-variable follow-up

This is an unexecuted design, not a proof or a frozen repository packet. The
preparer will require a matched 258-module comparator and explicit, truthful
tool-session observations of both parent process exits and of the comparator
wrapper exit. The marker schema is intentionally provisional until those exits
are actually observed. It constructs a regular-file 995-module source snapshot
and excludes all eleven rebuilt modules and their sidecars from the selected
parent overlay. The 848-project ancestor remains author-only; external package
transitive and dynamically loaded ancestry are inherited.

A source-current claim requires the parent comparator's
`workspace_matches_snapshot_through_observations` to be true, no drift in either
child replay's before and after scans, and no drift in a fresh final child
comparator scan. These are point-in-time observations, not continuous monitoring.

The replay and preparer must receive independent review before use. No code in
this directory modifies the active 258-module inputs.

The provisional `compare.py` and `run.py` require an explicit parent comparator
receipt matching both the child manifest's path/hash and its gate guard. The
receipt's workspace-match flag, both child replays' before/after drift scans, and
two fresh final scans determine the point-in-time current-source flag. The
wrapper records the comparator subprocess exit; its own exit must be separately
observed. `comparator-negative-checks-v3.json` records syntax and six missing-plan /
identical-directory / shared-state-inode negative checks, using both copied scripts
in each fresh directory. The v2 wrapper's missing-parent test failed earlier on
a missing copied comparator, so v2 is preserved as preliminary. An initial v3
checker assertion was too broad; its full reproduced failure is retained in
`check-negative-v3-initial-failure.log`, and the corrected checker passed. None
of these tests simulates successful parent evidence or validates a positive replay.
The scripts and updated preparer remain provisional and need independent static
review plus actual gated replay.
