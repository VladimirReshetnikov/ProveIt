# Uncompiled free-J 88-operation Lean bridge

This packet proposes a source-level bridge from the reviewed
[88-operation, degree-46 free-J graph](../ordinary13-ordinary-pair88-46/README.md)
to its 87-operation free-J parent and the parent's iPRA pipeline. **None of
these draft Lean files has been compiled or kernel checked.** The read-only
preflight is not a build-readiness approval, and no Lean process is run here.

`P88PairGraph.lean` contains the exact 88 named operations from the reviewed
JSON, with the same 13 free-J coordinates and four arbitrary integer ports.
It proposes an arbitrary-`CommRing` evaluation theorem: the new output equals
the parent graph's `A0²+A1²+(aux*strong−1)²`. The factored auxiliary gap is
related to the parent's difference of squares by a small ring identity; the
full high-degree carrier is not intentionally expanded. Syntactic graph count
and JSON correspondence are external checks, not Lean circuit-count or file
semantics theorems.

`P88PairModel.lean` proposes same-valuation `InternalZero` equivalence in
every IΣ₁ model for arbitrary integer ports. Parent-zero to new-zero uses the
existing `FreeJ13.factor_units` and `unit_iff_one`; the reverse direction uses
nonnegativity of the three squares, then the existing parent output formula.
No witness-coordinate change is involved. It then specializes the **same
free-J encoding** to `CompactSymbolicModelIff.p` and composes with
`FreeJ13Halt.positive_model_iff`. The final draft proposes the native,
standard and equality-only iPRA endpoints through the existing adapters.
The external all-signed-integer zero equivalence remains exactly the separate
mathematical proof in the reviewed candidate packet; this draft's proposed
model theorem does **not** by itself formalize that all-signed-integer claim.
In particular, it does not identify free J with P73's `3j+1` at the same
valuation.

Elaboration, `simp` ordering, casts, `linear_combination`, heartbeat use and
the three-square proof are untested. The existing parent endpoint has an
[author-side build record](../ordinary13-freej87-endpoint/README.md), not a
paired replay; its JSON/byte correspondence and inherited compiler/package/
dynamic ancestry remain external. No new Lean theorem, `totalDegree` result,
JSON or PDF binding, or proof of either side of the consistency statement is
claimed.

## Read-only preflight

From the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-freej88-lean-draft/preflight.py
```

The script pins the draft files, parent source, reviewed candidate and prior
P72-provider observation, compares all 88 source operations and coordinate/
port mappings, samples `/tmp` space, and point-checks five P72 frontier object
hashes. It observes conventional locations for `FreeJ13`, `FreeJ13Halt`, and
`IPRAOrdinary13` objects. These are filesystem observations, **not** a fresh
provider-closure or route/companion audit. The frozen
[observation](preflight-observation.json) records one sample; the 5.1-GB disk
stop was not met and free space is not reserved. The script always reports
launch blocked pending an independently reviewed guard and freshly
authenticated provider route.

One candidate staged route is to build the exact current `FreeJ13` and
`FreeJ13Halt` sources over the retained P72 provider, followed by these three
draft clients. The `IPRAOrdinary13` source itself need not be compiled if the
model client uses `FreeJ13Halt.positive_model_iff` and the already supplied
`IPRAOrdinary12Chain` adapters. This is a source-import plan, not an observed
build or compatibility theorem. A later guard must revalidate source/object
producers, direct paths and companions, overlay collisions and package inputs,
enforce the established disk/memory/time limits, and obtain independent
prelaunch review and exclusive Lean-slot allocation. No previous artifact
should be removed.
