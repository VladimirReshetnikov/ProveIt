# Trace75 to trace74 ring-coordinate probe

This packet checks a ring identity for the candidate in
[`trace74-mask-coordinate-probe`](../trace74-mask-coordinate-probe/README.md).
It uses the 75-row trace chart and its directly indexed BFS coefficient bytes,
which are different from the original-kernel tuple used by the checked 80-row
iPRA endpoint. The source is generic in all four ports; no coefficient or
machine theorem is assumed or proved here.

For any commutative ring, define `q = beta*J + 1` and replace the third old
input `alpha` by `q - F - C`. `Trace74Mask.coordinate_identity` proves that
`value74 p v = TenPositiveTrace75.value75 p (oldVal p v)`. Its proof factors
both sides through common downstream rows and applies `ring` only to the two
changed mask/rank arguments. `#print axioms` reports `[propext, Quot.sound]`.
This is an all-ring identity; it is **not** the positive-witness equivalence.
To map a positive new witness back to a positive old one one still needs
`F+C<q`. The converse requires positivity of the old mask `q-F-alpha`.
Neither implication has been established for trace75 zeros in this packet.
The trace75 all-model halt bridge, retained JSON/constant binding in Lean and
iPRA endpoint also remain open.

`Trace74Mask.lean` contains the explicit 74 operation rows and checks against
`TenPositiveTrace75.value75`; it uses ring values rather than the `Expr` syntax.
The read-only `check-rows.py` compares the Lean rows, witness and port slots,
and output to the pinned candidate JSON, including the accepted source and
provider receipts. Its successful `rows-check.stdout` is external evidence,
not a Lean proof about file bytes. `generate.py` records how the source was
constructed from package 163's pinned 75-row graph. It is a generation tool,
not a binding proof.

The upstream `TenPositiveTrace75.lean` was compiled freshly by
`run-provider.py` into `/tmp/trace75-provider-wljjm6ws` with accepted
`observations/provider-attempt01/`. Its object has SHA-256
`1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c`.
The identity passed using that selected object with `run-ring-v2.py`, accepted
`observations/ring-attempt02/`; object
`/tmp/trace74-ring-2m7vz_s6/Trace74Mask.olean` has SHA-256
`181b53fe5c5a52127a56ab25af95d0b7fda3d9842098850a70c8afc70659861e`.
The first ring attempt failed on a Lean identifier and vector notation and is
retained; its source snapshot and runner are separate. The accepted Lean source
SHA-256 is `83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0`.
Both runners pin their direct selected imports, record resource samples, enforce
an 8-GiB/two-process guard, and reject unexpected warning/error diagnostics.
Mathlib package transitive ancestry and dynamic dependencies are inherited;
no complete import-closure audit or independent Lean replay is claimed.
