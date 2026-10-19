# Checked internal control certificate

All 3,862 certificate entries and the assembled
[`ControlBisimRotation240`](../../Lean/BusyBeaver/ZFC/ControlBisimRotation240.lean)
now pass Lean. The resulting theorem equates halting of the Dag254 and
Rotation240 control interpreters from arbitrary internal register files in
every IΣ₁ model. The final binary-machine PA consistency theorem still
requires the remaining register/validator checks and composition.

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
preserves that measured result.

The remaining 30 intervals, covering entries `[128,3862)` without gaps or
overlaps, [pass individually](control-bisim-rotation240-leaves/batch.json):
30 probes and 30 typed callers, zero warnings. Their aggregate source and
audit times are 108.445 and 43.291 seconds. Each source/audit pair has its own
shared 120-second deadline, one thread and the unchanged 4 GiB cap. Each
source retains the original proof limits; each audit uses defaults.
The [leaf publication](results/control-bisim-rotation240-leaves-publication.json)
preserves the generation plan, individual results, logs and original failure.

The assembled public module now [passes eight probes and ten typed callers](results/control-bisim-rotation240-facade-verification.json),
with zero warnings and only standard Lean axioms. Source and audit took
2.023 and 1.774 seconds under the same resource policy. Its four original
interval statements are assembled from the 31 checked leaves using 27
applications of the joining lemma. The proof text from `check_all` through
the final `halts_iff` is unchanged. The
[publication](results/control-bisim-rotation240-facade-publication.json)
preserves the replaced source and its memory-failure evidence, alongside the
successful run. Splitting the certificate resolved that failure without
raising the memory cap.
