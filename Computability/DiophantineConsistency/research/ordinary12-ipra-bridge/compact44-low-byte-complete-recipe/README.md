# Closed 73,759-entry MC byte recipe

`generate.py` reads the hash-pinned retained parent `MC.bin.gz`, verifies
its raw and compressed hashes, and generates `CompactLowByteRecipeData.lean`.
The closed Lean `byteAt` function consists of the periodic dense-window rule,
11 explicit exceptional positions, the first byte, and default value 255;
`bytes` maps it over `List.range 73759`. The generator externally checks
the entire resulting rule against all 73,759 decompressed bytes and records
the 142 indices left outside the existing symbolic interval theorems. Its
source SHA-256 is
`62c1d80be22de3d88b1b19ec2ef0bcc588862fe6a3d844ceac3567192d33ea88`;
the successful `observations/generate-attempt02/stdout` SHA-256 is
`903ba8ae49a40bea6559d352f895c5694b90c1a1a8e0d990068c7324f971f516`.

The generated Lean source has SHA-256
`6cbe3f43fd7fad8e67b00339a12a468def8fb25eb7f343be675c97fdf155d394`.
The bounded author run `observations/attempt01` exited 0 in 1.795 seconds
without warnings or `sorryAx`, proving the list has length 73,759 and that
`bytes.getD j 0 = byteAt j` for `j < 73759`. The output object SHA-256 is
`a91925db9780268cc67d0a91c12cd6b1b8987e661bb80c2736bfd76001de1320`;
direct dependency and companion guards were unchanged at the recorded
points. The earlier generator version and output are retained under
`generate-attempt01`; the second adds the explicit `List.GetD` import.

**No global Lean equality between this byte list and `lowNat` is proved in
this packet.** In particular, the generator's whole-payload comparison,
Python transcription, file and gzip identity are external provenance. The
142 remaining symbolic windows need checked proofs, followed by an
all-index assembly and the generic radix-window reconstruction theorem.
The parent/supplement, PDF and iPRA bindings remain separate obligations.
This is an author-side check over inherited package ancestry, not a paired
replay or full transitive/dynamic audit; guard checks are point-in-time.
