# Expanded compact/iPRA rebuild: stage 95 timed out

This bounded author batch resumed the corrected 425-module merged-root build
after 94 stages and checked all pinned sources, selected original and merged
provider files, prior output/log hashes, direct dependency and companion guards,
and the three source-pinned exact warning baselines. The runner SHA-256 is
`c3c11a6e5f29fa79bf70d6d1c05d1b914b5933c49b765f5370fbcbba011e4846`.

The first requested stage, `BusyBeaver.ZFC.ArithmeticDagControlPerm222`, hit
its 180-second subprocess wall timeout. The wrapper recorded a null child exit
and no output object; its source and direct dependency guards remained
unchanged, and it stopped before the full post-batch overlay check. The raw
empty compiler log, source snapshot, dependencies, guard inventory and receipt
are under `observations/batch-019/stage-0095/`. This attempt is not a proof.

The source has 251 physical lines and 55,875 bytes, SHA-256
`1851444d564e63c2296c2e64335d95008465da9c1fd837bef399886f691e7fb4`.
Historical author and root replay `.time` files under
`reviews/arithmetic-dag-controlperm222-{author,root}-replay/` record successful
builds of the named source in approximately 7:48 and 7:55, at about 2.91 GB
peak RSS under Lean `-M6000`. The saved author source snapshot in
`reviews/ha87-full-source-build-author2/source-snapshots/` has the same source
hash, but these historical timings do not authenticate the current overlay or
guarantee a retry succeeds. A separately guarded, longer wall-time retry can
preserve the 3,000 MB Lean setting and keep all prior evidence; actual runtime,
memory behavior, warning status and full guards must be reported.

No iPRA endpoint or complete provider audit follows from this stopped prefix.
Package, dynamic, inherited source-to-object ancestry and subsequent stages
remain open.
