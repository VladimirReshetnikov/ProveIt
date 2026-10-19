# Splitting the internal control certificate check

The [original combined check](rotation240_pa/control-bisim-first-check/README.md)
hit the 4 GiB memory limit. The replacement separates finite intervals of
the same 3,862-entry certificate and then joins their proofs. The packed
tables, certificate and required public halting-equivalence statement stay
the same.

The shared definitions and interval-joining lemmas in
[`ControlBisimRotation240Common`](../../Lean/BusyBeaver/ZFC/ControlBisimRotation240Common.lean)
have now [passed Lean](results/control-bisim-rotation240-common-verification.json):
two probes and two typed callers, zero warnings, default proof limits.
Source and audit took 1.579 and 1.420 seconds under one thread, 4,096 MiB
and a shared 120-second deadline. The guard reuses 38 exact project
prerequisites and three external boundaries from the actual DagControl
check, with Init/Omega. All reported axioms are standard Lean axioms.

The new lemmas join two adjacent passing intervals. They do not evaluate
any concrete certificate entries. The [publication](results/control-bisim-rotation240-common-publication.json)
preserves the actual check and the source-only partition proposal: 31
intervals of at most 128 entries, aligned with the original four intervals.
The first concrete interval, entries `[0,128)`, now
[passes](results/control-bisim-rotation240-pilot-verification.json) one probe
and one typed caller with zero warnings. Source and audit took 3.272 and
1.383 seconds, keeping the 4 GiB cap and shared 120-second deadline. Its
source retains the original recursion limit 100,000 and unlimited
heartbeats; the audit uses defaults. The
[pilot publication](results/control-bisim-rotation240-pilot-publication.json)
preserves that measured result. The remaining 3,734 entries still need checking.

The original public facade has not yet been replaced. Its full finite
coverage, initial entry and arbitrary-model halting equivalence still need
successful compilation against all the proposed interval proofs.
