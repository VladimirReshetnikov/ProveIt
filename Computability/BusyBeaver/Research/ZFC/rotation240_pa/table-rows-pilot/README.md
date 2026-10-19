# Checked packed-row pilot for Rotation240

[`TableRowsRotation240Pilot`](../../../../Lean/BusyBeaver/ZFC/TableRowsRotation240Pilot.lean)
checks the twenty decoder leaves at full path `111010010010101111110110`,
controls 6228–6247. Each check compares the opcode, physical register and both
stored successor fields against the packed interpreter table. This uses the
checked counted tree and generic table-binding theorem.

The [actual run](../../results/w6-table-rows240-pilot-verification.json) passes
one axiom probe and one typed caller with zero warnings; its only reported
axioms are `propext` and `Quot.sound`. Source and audit took 1.628 and 1.412
seconds, respectively, under default proof limits, with one thread, 4,096 MiB
and a shared 120-second deadline. It reuses 46 checked project prerequisites,
three external cache boundaries and Init/Omega; dependency caches were not
rebuilt or wholly attested.

The first attempt failed during parsing because `prefix` is a reserved Lean
token. The successful source renames it to `cutPath`, preserving the path and
proposition. The failed attempt, original source reviews, repair and accepted
logs are retained in the [history](history.json.gz). The
[publication record](../../results/w6-table-rows240-pilot-publication.json)
identifies the accepted files; historical scratch paths are retained.

The partition comes from the previous binary-site coverage proof. Its old
proofs are not used as evidence of this different row-equality proposition.
This pilot alone does not establish the full table equality or the internal
binary simulation. Attribution for the underlying construction remains with
Mira-Cult, Jeff Ketchersid, Andrew James Wade and the maintained ProveIt work.
