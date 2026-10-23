# Shared decrement prefix — research lead

**Not adopted. The repaired component and three-block benchmark pass.**
[Terminal result](benchmark/v2/result.json) and [independent actual readback](benchmark/v2/actual-review.json)
bind this isolated experiment, separate from the phase25 checked sources.

The proposed `runDecnz` executes a neutral prefix once to an explicit symbolic target:
state 0, head right, and a singleton right list containing the matching physical-register mark.
The complete returned intermediate configuration, including its left list, is retained.
Branch validity supplies neutral validity; `moved=false` makes the prefix reach positive.
For either valid branch, its specialized zero/nonzero tail starts at that exact configuration
with the same valuation and `moved=true`, allowing a reflexive tail. Existing soundness composes the reaches.

The [v2 KSim snapshot](source/KSim.lean) adds **36 lines / 1,580 bytes** against the
[phase24 source](source/before-KSim.lean); [full record](source/candidate.diff.json) and [repair](source/repair.diff) diffs are explicit. The full record preserves the raw UTF-8 diff and hash inside JSON;
the original raw patch remains in the archive.
The checker intentionally changes Boolean acceptance; equivalence with the old fuel policy is unproved.
Model-core sources, machine data, decrement targets and public theorem signatures are unchanged.

The isolated comparison fixes the accepted phase24 dependencies: 19 modules, 17 exact unaffected
reuses per arm, and fresh KSim plus KFastSites215 in each arm. An identical fresh probe then checks
production blocks **0, 5, 10**, with **9, 52, 67** literal leaves and their unchanged `decide +kernel` proofs.
The [controls](benchmark/v2/README.md) retain the shared lock, serial compiler/resource limits,
zero-warning rule, exact profile comparison, input/object/log bindings and new-only output directories.

[V1 failed](benchmark/v1/failure/result.json) before either block probe: two closed `if true=true` /
`if false=true` targets blocked the existing target rewrite. V2 adds only explicit branch normalization
before each unchanged rewrite. The [repair peer](source/repair-peer.json) and
[control peer](benchmark/v2/independent-peer.json) preceded the later successful compilation.
V1 sources, controls and raw failure records remain preserved; its objects are never reused.

Both baseline and repaired-prefix arms compile all three blocks with identical profiles and zero warnings.
The observed compiler times are **19.4633s baseline / 17.0279s prefix**, excluding
lock wait. This is one ordered sample per version; no general speed claim follows.

Detailed attempt/workspace histories belong in the [evidence archive](../../lean/evidence.tar.gz).
This public subset omits cache objects and repeated workspace trees. One ordered three-block sample
cannot establish acceptance of all 45 K-family batches or all 6,176 outcomes, general performance,
production adoption, a smaller machine, or a completed PA endpoint. The machine remains 215 states.
