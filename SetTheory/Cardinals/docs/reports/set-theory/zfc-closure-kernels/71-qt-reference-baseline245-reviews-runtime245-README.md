# A 245-state binary Turing machine: runtime and source certificate

The exact deliverable is `certificate/machine.tm`: 245 working states numbered
0–244, blank-zero initial tape, initial state 0, and target-only halt state245.
It has 490 binary transition rows. The old-label equivalent is
`certificate/machine_old.tm`; the bijective mapping is in `renumbering.json`.

Canonical SHA-256:
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.

The construction combines128 shared decoder grammar states with117 remaining
framework states. It removes the fixed routing role of old state177 and
shortens the scanner by removing the fixed role of old state74. The successful
grammar has maximum source zero run6, leading-zero depth3, and maximum path
depth51. State labels can be reused by the rebuilt grammar; the saving counts
implementation roles, not prohibited numeric names.

## Reproduce the mathematical certificate

From any directory, with Python3.10 or newer:

```sh
python /absolute/path/to/this/package/code/verify.py
```

No solver, compiler, external package, network, or proof assistant is needed.
The command writes a fresh temporary replay directory and prints its path.
Use `--output /chosen/replay/directory` to select one. Assertions must remain
enabled; do not run Python with `-O`.

The default command checks the supplied file hashes, verifies exact
source-body equality for the declared padding adaptation, rebuilds the literal
machine, re-parses the pinned original program, regenerates and independently
checks the3013-pair register bisimulation, checks every one of8391 guarded
instruction cases, and replays the exact407915-step blank bootstrap with sparse
and dense tapes. It then independently derives every register macro contract
on this actual table by unary and finite-list induction before performing a
second complete8391-case affine replay.

For an independent whole-frame replay with all nine registers represented by
separate arbitrary natural variables and an arbitrary nonempty spare suffix:

```sh
python code/verify.py --whole-frame
```

This optional independent pass takes several minutes. Its literal, unary and
finite-list proof rules are unchanged from the inherited whole-frame checker.
It expands the register boxes instead of assuming their opaque contracts.
The default macro proof already quantifies all values and spare lists.

## What the certificate establishes

The tape frame uses an arbitrary header distance64+n for every natural n.
The concrete blank initialization gives181, so n117. Positive decrement and
pointer overflow can increase this distance; no source instruction decreases
it. Every complete instruction has positive finite runtime. The nonempty
spare list is preserved, with increment appending a spare of value1.

The exact initial logical register vector is
`(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`. Composing the verified runtime and
register bisimulation with the pinned ProveIt dirty-root theorem and the
upstream SIR/ZFC consistency comparison gives the ordinary ZFC proof discussed
in `proof/zfc245_runtime_proof.tex`:

`ZFC proves: M245 does not halt on blank tape iff Con(ZFC)`.

The new certificates are ordinary mathematical certificates checked by small
Python programs. A new Lean/Rocq kernel endpoint for this exact245-state table
is not included. No consistency assumption is needed to prove the equivalence,
and the certificate does not claim an unconditional ZFC proof of nonhalting.

## Files and provenance

- `grammar.json`: the concrete128-rule search result; search is not trusted by verification.
- `inputs/`: pinned sequence grammar, context-labelled atomic programs and orientation information.
- `certificate/`: machine tables, state allocation, full source paths, finite bisimulation,
  complete blank frame, and audit summaries.
- `certificate/independent-runtime/`: actual-table universal macro induction traces and audit.
- `code/`: portable reconstruction and checking commands, including the explicit padding adaptation.
- `reference/`: attributed inherited code and original sources, with notices and licenses.
- `proof/`: the runtime/composition and transparent-routing/bootstrap mathematical notes.
- `provenance.json`: original source paths, source hashes, repository commits and adaptation scope.
- `manifest.json`: SHA-256 values of the curated package files.

The primary pinned repositories are ProveIt
`c6bf052c70bbbafba8c39370a6a2d123f57cd2c1` and jeff87654/busy-beaver branch
zf-254 at`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. The inherited research
archive is preserved through the referenced source files and notices. The
manifest attributes every copied source before portability-only path changes.
