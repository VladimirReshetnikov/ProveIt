# Expanded compact/iPRA rebuild: stopped at stage 266

Stages 264–265 compiled cleanly, with source, dependency and object receipts
retained. Stage 266, `ZFCinPA.ModelCodedDecoderCollection254`, exited 0 in
7.292 seconds but emitted eleven linter warnings: unused simp arguments, an
unused and unreachable `rfl`, and unnecessary tactic sequencing. The runner
rejected its object and stopped without running later stages. Source and direct
dependency guards were unchanged. The rejected object SHA-256 is
`1cae5502955e62c4f5838b1f53e043cc73b2ab8c196b8608fe3181c9b86b5975`.

Runner SHA-256 is
`5111d5aac1eed68987fea5e90a8da9ee516e6394cfc8023e2e81dbd6502c6186`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,457,716 KiB; brief children and overlap can be missed. The author
prefix through stage 265 is not an iPRA endpoint, independent replay, or full
provider audit. The rejected object requires quarantine before replacement.
