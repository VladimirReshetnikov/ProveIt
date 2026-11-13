# Expanded compact/iPRA rebuild: stopped at stage 250

Stages 240–249 compiled with exit code 0 and no warnings; their sources,
guards, logs, timings and object hashes are retained per stage. Stage 250,
`ZFCinPA.ModelCodedDecoderRho4_254`, exited 0 after 2.645 seconds but emitted
three `unnecessarySimpa` linter warnings. The runner rejected its output and
stopped; no later stages ran. Its source and direct dependency guards remained
unchanged. The rejected object SHA-256 is
`417c68884d4f44ded4c2a8beccc05f85ee10739a49057c2bf6427acc82d918d5`.

Runner SHA-256 is
`91b0e60043119aa9a070208ea8df26cf91a256f69bbfbb565884e4f003cdd886`.
Five-second monitoring sampled at most two Lean children during authorized
overlap and minimum MemAvailable of 17,948,984 KiB; short overlap can be
missed. The prefix through stage 249 is not an iPRA endpoint, independent
replay, or complete provider audit. The warning-bearing object is rejected
unless separately quarantined and replaced by a guarded, source-pinned retry.
