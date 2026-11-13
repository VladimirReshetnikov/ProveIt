# Uncompiled free-J 88/30 four-square bridge

This source-only packet proposes the graph, model and iPRA clients for the
independently reviewed [four-square candidate](../ordinary13-four-square88-30/README.md),
using the separately reviewed but **uncompiled** [88/46 parent draft](../ordinary13-freej88-lean-draft/README.md).
None of the new or parent draft files has been elaborated or kernel checked.

`P88FourSquareGraph.lean` lists the candidate's 88 operations with the same
13 free-J coordinates and four arbitrary integer ports. Its proposed
arbitrary-commutative-ring theorem identifies its output with
`(A0²+A1²)+((Fa−1)²+(Fs−1)²)` using the parent's residuals. The graph itself
uses its live `g72` directly, with `Fs=1+g72`; it does not add an `Fs` gate.
Operation counting, liveness and correspondence with JSON remain external.

`P88FourSquareModel.lean` proposes `InternalZero` equivalence to the 88/46
parent for the **same valuation**, arbitrary integer ports and each IΣ₁ model.
The four-square-to-parent direction extracts four zero residuals from their
nonnegative squares. The reverse uses the parent's proposed zero equivalence
and the existing `FreeJ13.factor_units` and `unit_iff_one` results. No witness
translation or identification with P73's different `3j+1` encoding is used.
It then composes the parent's proposed positive-zero/halting bridge; the
endpoint client proposes the native, standard and equality-only iPRA transfers.

The reviewed external argument establishes both zero directions over all
standard integer valuations and exact specialized degree 30. This draft's
proposed model theorem does **not** formalize that separate all-signed-integer
claim or its degree certificate. It does not prove either side of the endpoint,
bind JSON, byte files or PDF text in Lean, or replay the inherited endpoint.
The existing author-side endpoint and its historical package/dynamic ancestry
retain the qualifications in the parent packet. Elaboration, tactic behavior,
casts, simplification and resource feasibility are untested.

The included `preflight.py` pins candidate/review and parent source/review
records, checks the literal rows and port mapping, and samples disk space. Its
[observation](observation.json) is point-in-time source evidence only. The
[provider survey](../ordinary13-freej88-provider-survey/README.md) describes a
historical single-P72 route for the parent, not a future compatible overlay or
complete package/dynamic ancestry; these three new clients add dependencies
that require their own fresh route and collision checks. No guarded runner is
provided and no Lean run is authorized below the 5.1 GB sampled disk stop.

From the repository root, run:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-freej88-four-square-lean-draft/preflight.py
```

`make_graph.py` generates the graph from the pinned JSON and refuses to overwrite
an existing file. Neither script invokes Lean or creates a build tree.
