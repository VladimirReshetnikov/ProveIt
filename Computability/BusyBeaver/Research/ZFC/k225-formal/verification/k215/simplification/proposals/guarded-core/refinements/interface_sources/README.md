# Exact M124 transfer in Lean

`Marker124.all_tapes` proves that the exact M124 native table and the accepted
K215 native table halt together on every head-centered binary tape from control
zero. `Marker124.blank_nonhalting` specializes this to the blank tape.

This is a new proof of the existing M124 construction from the DR215 marker
appendix. Its creation is not claimed here. The pinned repository revision is
`e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`.

## Mathematical contract

The old-control invariant has two marker clauses:

* At old 124, the bit immediately left of the head is 1.
* At old 127, the bit immediately left of the head is 0.

Old 127 maps to new 124. All ordinary steps transfer in one step; the two
zero-reading exceptional roles transfer in three steps. `simulate` proves
matching times `n <= k <= 3*n`. The reverse halting argument uses positivity
and an absorbing halt; it does not assume that forward simulation alone proves
equivalence.

The tape is `Int -> Bool`, centered at the current head. Equality is equality
of the entire centered tape; the companion Rocq proof carries an explicit
absolute integer head position. The default transitions on unused native
labels are a harmless total extension: `old_reachable_states` and
`new_reachable_states` prove that only the 215 counted working labels or halt 254
can be reached from control 0.

## Checked data and trust

`Marker124Data.lean` contains the exact 430 baseline rows, the exact four-row
M124 patch, and kernel-reduced finite facts. It verifies incoming markers,
ordinary-row commutation, the 215-state count, distinct labels, initial membership,
separate halt, and closure of both tables.

`generate_data.py` reconstructs that entire file from the exact pinned K215
native table; `--check` compares the generated source verbatim. The generator
is untrusted: the emitted propositions are checked by Lean's kernel.

The recorded toolchain is Lean 4.32.0. Both theorem assumption reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. No new axioms, admissions,
`sorry`, `native_decide`, or unsafe proof evaluators are used.

## Reproduction

From this directory:

```sh
python3 reproduce.py --lean /path/to/lean
```

The driver uses a fresh build directory, checks exact generation, compiles both
modules, rejects warnings/admission reports, and records compiler version,
source hashes, commands, logs, and exit status. The saved run is in
`verification/`.

The report's integration boundary applies here: the existing repository ZFC
endpoint is not imported into this standalone tape model yet. Port the local
marker proof to `KZip`, or prove a reusable configuration-model bridge, before
advertising a newly integrated Lean ZFC endpoint.

Original table and marker-machine attribution is preserved in
`../m124_rocq/UPSTREAM_NOTICE.md`. New proof material follows ProveIt's MIT No
Attribution terms; the unchanged repository license is supplied.

