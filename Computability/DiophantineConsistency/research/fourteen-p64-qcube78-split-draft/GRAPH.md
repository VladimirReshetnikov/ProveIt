# Actual-zero first residual for the 78 graph

`P64QCube78GraphSplit.first_eq_one` proves that every positive zero of the
78 graph, for arbitrary natural ports in the stated IΣ₁ models, has first
residual equal to 1. It first obtains `P≥1` and `k>0` from positive inputs,
applies the near-square exclusion and five-square lemma to get the first
square equal to 1, and sends the four remaining squares to the checked
arbitrary-first residual splitter. Its transport zero then forces the first
port positive, whence `q≥2` and `P≥2`. The consecutive Pell lemma rules out
the negative unit, so the first residual equals 1. This theorem is a model
result for the Lean graph; zero-equivalence and iPRA endpoints are separate.

The corrected Lean check (session 75574) exited 0 and reported the axioms
`[propext, Classical.choice, Quot.sound]`, with no warnings or `sorryAx`.
The preceding session 23701 failed with two elaboration errors and an
unused-simp warning, which were corrected before the successful check.
The successful check used the same command and search path as the generic
check in [README.md](README.md), with source and output respectively changed
to `P64QCube78GraphSplit.lean` and `/tmp/P64QCube78GraphSplit.olean`.

These hashes were recorded after the author check. This is not a guarded
before/after replay or a complete transitive source-to-object rebuild.

| File | SHA-256 |
| --- | --- |
| `P64QCube78GraphSplit.lean` | `f0bb74cf05302f5067a0f99fbb4f5b8f63e9cb75ad11154bc82b0219004c5020` |
| `/tmp/P64QCube78GraphSplit.olean` | `76da5f69b14d211994c5ccc12e9e9de9d5d3b585b002149bca4922d7ca536150` |
| `/tmp/P64QCube78.olean` | `112e4979a76e241719cbb1b682e98c8cebabb3150c3349055dd6964ed12be0f5` |
| `/tmp/P64QCube78Split.olean` | `ccdfdcbee3c4de43f2bb3924fcbdeade0eb2b7e0cc9a99e1d64bf07e52ddced9` |
