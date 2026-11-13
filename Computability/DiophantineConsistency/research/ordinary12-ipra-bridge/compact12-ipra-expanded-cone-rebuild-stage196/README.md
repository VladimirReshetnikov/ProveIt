# Expanded compact/iPRA rebuild: stages 196–197, stopped on warning

This bounded author batch resumed the corrected guarded 425-module merged-root
build after stage195, revalidating all prior runner hashes, baselines,
quarantines, 425 source hashes, selected original and merged provider files,
prior output/log hashes, three exact-warning baselines and direct dependency
and companion guards. Before each new stage it required at least 8 GiB
MemAvailable and fewer than two existing Lean processes. The runner SHA-256 is
`dec186238774609f31e73c1dd338d14d8ef1d3fb1c4e729252890cca84f30dbc`.

Stage196 (`KQ1Separation`) exited 0 without warnings; its recorded direct
source and dependency guards were unchanged. Stage197 (`KQ1Basic`) exited 0
but warned that the explicit `witness` binder in `interpreted_pair` was not
referenced. The runner rejected this unbaselined warning and exited 1 before
the full post-batch overlay check and stages 198–200. The stage197 object
SHA-256 `fd61d67e686d620b818bb53cca8d9e2eb2fa49c6cd70731bfdffea92c078c171`
is rejected and must not be imported as a successful result. Exact source,
dependency lists, logs and receipts are in `observations/batch-040/`.

The named `witness : V` is an explicit argument of `interpreted_pair`, which
`quotient_pair` calls positionally in the same file. Removing or renaming it
should not be assumed to preserve the named interface. A separately reviewed
exact source-pinned warning baseline or independently checked interface-
preserving correction and fresh guarded retry are required before resuming.
This packet does not establish successful stage197 or an iPRA endpoint.

`observe_run.py` sampled Lean processes and memory every five seconds: none
of three samples captured a Lean process, and minimum sampled MemAvailable was
18,627,124 KiB. These sparse samples do not imply no Lean process ran. Exact
sampled data are in `observations/execution-monitor/monitor.json`. This is not
an independent replay or full package/dynamic/provider ancestry audit.
