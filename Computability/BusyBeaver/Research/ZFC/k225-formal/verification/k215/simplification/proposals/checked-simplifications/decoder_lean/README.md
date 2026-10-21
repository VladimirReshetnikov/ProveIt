# Framed decoder blocks for exact K215

This component completes a local formal foundation of the incoming finite
decoder-product proposal. The data architecture is inherited; the generic Lean
proofs, executable checker and their concrete instantiation are supplied here.

## Statements

`FramedWindow.lean` defines finite known tape cells and an evaluator that rejects
before reading an unspecified cell. A proved refinement theorem lifts any
successful local execution to the complete integer-indexed tape. Its translated
form works at every head location. When the local block restores its cell list,
it restores the entire arbitrary tape, including the unspecified exterior.
The generic list semantics uses the first matching coordinate; duplicates do
not invalidate the theorem. Concrete windows have distinct consecutive cells.

`DecoderCertificate.lean` defines positive-duration blocks and a separate finite
structural checker for source nodes and decoder roles. A `Chain` relation carries
the exact window premise at every location. `chain_sound` concatenates any finite
chain using the full machine's run-addition law.

`K215Decoder.lean` contains the exact native table, 202 source DAG nodes, 234 roles,
and 281 distinct blocks. The product has 371 internal and 97 primitive-entry edges.
The block widths one, two and three have counts 252, 25 and 4; the maximum duration
is seven steps. All local windows include the currently scanned cell. The source
expands to the pinned 4,751 primitive occurrences.

The concrete `certificate_checked` combines all block checks with finite
structural checks. `restores_arbitrary_tape` and `certifies_block_chains` instantiate
the generic semantic results. Explicit malformed examples are rejected.

## Trust and remaining obligations

All three modules compiled afresh under Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, in 41.646 summed compiler seconds.
The literal block-acceptance theorem has no axioms. Semantic theorems use only
`propext`, `Classical.choice`, and `Quot.sound`. There is no `sorryAx` or
`native_decide`; the generator is not a logical premise.

The independent audit imports no generator. It binds all 430 native actions,
all source nodes and roles, and expansion to all 4,751 sites. It replays every
block, checks role reachability, and rejects malformed block/structural controls.
It also demonstrates intentional scope boundaries: structural validity alone
does not check positive duration or primitive argument semantics.

The expansion binding is currently ordinary Python evidence, not an in-kernel
identity with upstream `KSource215`. Theorems for source paths producing `Chain`
window witnesses, primitive semantics, register boxes, pointer returns and full
site coverage remain to be attached. This component does **not** replace
`KSites215`, prove the complete source runtime, or rebuild the ZFC endpoint.

## Reproduce

```sh
python3 audit/audit_decoder.py . --out /tmp/decoder-audit.json
python3 build.py --lean /absolute/path/to/lean --out /tmp/decoder-fresh
```

The first command is an ordinary independent audit. The second creates a fresh
directory, regenerates the data, requires a byte-for-byte match with the checked
Lean source, and compiles the modules serially without importing project objects.
It records source/object/log hashes and assumption reports in the output.

`verification/receipt.json` and its logs record the successful fresh build.
`audit/evidence.json` records the independent final-data audit. Toolchains and
compiled objects are excluded.

## Provenance

Repository pin: `53269bcab1efc0f82d3022645bd7cf0c22d84959`.
The native machine and site list are exact pinned primary K215 artifacts.
The product JSON is from incoming I7,
`zfc-fm215-proof-compression-2026-10-21.zip`, with SHA-256
`9dc3d2fb25020992de466b2d91eb15f00539da585d9e6219bb372e6352c7beff`.
The 281-window proposal also appears in I4 and is not a new discovery here.
Generation and independent-audit records bind all inputs and outputs.
The repository's MIT No Attribution license is reproduced in `LICENSE.ProveIt`.
