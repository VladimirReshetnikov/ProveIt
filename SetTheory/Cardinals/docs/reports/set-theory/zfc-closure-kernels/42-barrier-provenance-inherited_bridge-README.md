# Selected inherited universal program bridge

These are unmodified source files selected for provenance and inspection.
They are not a complete build of either upstream project. Their original
repository paths and commit identifiers are in `source_manifest.json`,
together with independently checked Git blob hashes and SHA-256 values.
Upstream authorship and licensing apply unchanged.

The Coq files come from `jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`.
The Lean files come from `VladimirReshetnikov/ProveIt` commit
`61e77836565f63582561f54745f633d50efd9c7d`.

## Direct theorem composition for arbitrary W,T

Put `s = mkState 0 0 T W 0 0` in abstract enumerator field order
`(pl,np,tw,ws,d,h)`. Let R have source entries
`[0,T,W,0,0,0,0,0,0]` and be zero above index eight. Then
`approx R (enc s)` holds by evaluation. Physical order, defined by
`Check254.phys_order`, gives `vregs R = [W,0,0,0,0,0,0,T,0]`.

The universal Coq theorem chain is:

```
Bisim254.p254_dag R
  : rm_halts p254 ([],R) <-> rm_halts dag254 ([],R)

RMEquiv.rm_halts_iff_iter dag254 Main254.dag254_wf R
  : rm_halts dag254 ([],R) <-> iter_halts dag254 R

L2Root254.iter_halts_dag s R
  : approx R (enc s) ->
      iter_halts dag254 R <-> L2Root254.halts_from s
```

The first theorem uses the entire explicit `Cert254.v` in both directions
and the sound finite checker from `Bisim.v`. The second requires only the
program well-formedness theorem. The third requires only the encoding
equality. None requires that the formulas or initial stack contents be
theorems. The blank-only corollary `Main254.prog254` is not needed here.

The root configuration's nonzero spare tape blocks are the separate
`ext` field of the physical invariant, not source register values beyond
index eight. The physical simulation transport and new arbitrary-stack
soundness argument are documented in the independent runtime review.

## Identical DAG in the two proof languages

The Lean `Dag254.lean` explicitly attributes its source to the pinned
Coq `Dag254.v` with SHA-256
`538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`.
That value matches the enclosed Coq file. `L2Root254.lean` and
`RMEquiv254.lean` contain the corresponding universal root and
structured/path theorems. The original 6459-node decoder tree is
`coq/tm/Prog254.v`, Git blob
`254106e2b20762ddd89b2fad4765af5248d41469`, SHA-256
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
It is byte-identical to the frozen source used by the new runtime package.
