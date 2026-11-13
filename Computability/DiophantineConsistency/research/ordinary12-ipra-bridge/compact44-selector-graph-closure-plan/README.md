# Preliminary graph-selector source closure

This is a source-only plan on the independently audited paired same-witness
saturation provider, not a build. The proposed same-side topological order is:

1. `CompactPositionIncrement`, from commit `ecafb6225a`, SHA-256
   `38c19700d6caeadd28bae9d239b0c2302e032ec01011071ea4b4ace52543a675`;
2. `CompactPositionGraph`, from the same commit, SHA-256
   `23ede19121f1691051f8667833b99baf09090af765ecc88c2357a74501cb715c`;
3. `CompactSelectorMask`, from commit `cfa2403812`, SHA-256
   `91846742919ca2a0d3ffce3a6da0b7cac2044de2d9ef6fc6b640c329431df550`;
4. `CompactSelectorGraph`, from commit `e90ea00818`, SHA-256
   `dfd3155e95af8d17e6ee46a3eb37d0f40a8ad429febb1caf23dae8f2a1bc447b`.

The first two sources additionally use `CompactMixedIncrement` and
`CompactSameWitnessSaturation2` respectively from the corresponding parent
side. The remaining project imports must resolve to earlier new outputs on the
same side. A future driver must use fresh overlays of
`/tmp/ipra-same-witness-saturation-pair-01/{author,peer}/lib` and reject all
pre-existing target slots; it must not reuse the scratch exploratory objects.

The no-Lean scanner checks each source against both its exact hash and
committed Git bytes, its import list and exact `#print axioms` names, the
pinned independent parent audit and terminal observation, and topological
availability. It compares 146 `.olean` paths and hashes across the two
parent sides and records 40 external direct companion slots, 80 absent target
slots, and ten package Init slots. Corrected scan session 18154 exited 0;
optimized Python exited 1. The first scanner attempt exited 1 before
producing a result because it treated inventory path strings as `Path`
objects; that source is retained under `observations/attempt01.py`. These are
point-in-time observations; the scanner does not rerun the parent audit or
authenticate all package, transitive and dynamic ancestry.

A future paired driver must independently rerun and compare the full parent
audit, freeze and recheck the four exact sources, enforce same-side direct
imports, guard input/output companion slots and Init, and compare the paired
outputs. It must check all eight exact report names (counts 1,2,2,3, listed
in `scan.json`) and the observed `[propext, Classical.choice, Quot.sound]`
sets, reject warnings/admissions, capture actual child and outer exits, and
record resource and dependency-query boundaries. Independent prelaunch and
post-build reviews, a trusted clean initial loader, stable HEAD and sole Lean
slot remain required.

The exploratory final theorem assumes fixed symbolic beta/low/high ports,
arbitrary natural K, positive graph coordinates and the literal graph zero.
For the same N,w it proves selector digits at most one for standard
`j<943`, `j≠1`, when model `k` is positive, below `8807*N`, and has residue
`j`; it proves residue 1 zero under the same position bounds, with the origin
handled separately. This plan does not bind the retained tuple, construct or
rotate a word, prove the local decoder premise, establish a machine
simulation, or produce an internal iPRA proof.
