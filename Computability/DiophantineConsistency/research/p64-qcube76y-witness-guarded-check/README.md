# Guarded conditional 76Y witness maps

`IndependentYWitnessDraft.lean` proves model-level positive magnitude and
positive difference representatives, an old→new positive-zero witness map
under the nonzero signed-root guard, and a new→old map under the strict-root
guard. Both guards have separately checked actual-zero proofs; their join
and the resulting positive-zero equivalence are separate clients.

The [second bounded check](observations/attempt02/result.json) exited 0
with four `[propext, Classical.choice, Quot.sound]` reports, no warnings or
`sorryAx`, and stable direct provider/source guards. Its object
`/tmp/p64-qcube76y-witness-priority-check02/IndependentYWitnessDraft.olean`
has SHA-256 `6c72bd3c908ef240f7aeace9387e4126d0ac7ca47e52a81919c7ba8b007c39c0`.
The corrected source SHA-256 is
`b4f83f52f59bc0630b68cb5a301869e50e7805369ea86cd0b17d3a4fb906b51b`.
The [first attempt](observations/attempt01/compile.log) exited 1 because a
local `z` definition was not unfolded in a cast equality; that unresolved
declaration reported `sorryAx`. Its exact source, log and receipt are retained.

The successful run used `-M2400`, nice 19, idle I/O, a 120-second limit,
and sampled stops at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`,
alongside the current14 rebuild. It recorded 24 group-RSS samples, sampled
maximum 2,106,589,184 bytes and minimum available memory 16,959,815,680 bytes;
no stop fired. Sampling is not a hard RSS reservation. Captured-provider
transitive and dynamic ancestry remains inherited; shared monitor controls
are in the [graph packet](../p64-qcube76-independent-y-guarded-check/README.md).
