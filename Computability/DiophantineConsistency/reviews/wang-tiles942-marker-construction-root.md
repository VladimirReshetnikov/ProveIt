# A constructed cycle's unique marker and its quotient transport

Date: 2026-10-26. Author: ROOT. This is an author receipt for two new
main/check pairs, completely read before capped Lean execution.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942CycleMarker.lean (70 lines) | 2806b219857cfc334bc502fc15eccbebf0f6206a381c2e809029905e7d9076c5 |
| WangTiles942CycleMarkerChecks.lean (40 lines) | 837a916c03a244f7ad535d1fa27e5fab0729beeb7c92d5b077bc746606822873 |
| WangTiles942HelicalMarker.lean (60 lines) | 55962b759130f61cb138afde6a87796da4a12ddf7b0bc891a2d2417da2c788c7 |
| WangTiles942HelicalMarkerChecks.lean (34 lines) | e32e73c910ef7e6b676ce4a0c3e6d15ad7427f998bf81ba5082f6d7db090830b |

The initializer has north435 exactly at spatial coordinate0. All actual
machine colors are≤433 and reset has north438. Thus the constructed
cycle has Start exactly when its finite row index is0 and x=0. This
statement needs no halt or minimum-height premise, since it concerns
the explicit tuples only; it does not claim temporal matching at an
invalid height. The height1 checks retain that distinction.

The helical helper assumes an explicit local classification on the
canonical band: C(x,t)=Start iff x=0 and t%H=0. It proves that the exact
quotient of the Euclidean extension has Start only at cyclic index0.
For a canonical representative z.val, a zero spatial representative
gives−z.val=w*q. The time condition gives H|q, hence w*H|z.val. Since
0≤z.val<w*H, it follows that z.val=0. Conversely0≤L<w keeps the origin
inside the band and its quotient zero. No coprimality is required.

That local classification remains an explicit helper hypothesis;
applying it to the actual constructed band is separate work. This
packet does not add a unique-Start premise to general marked-word
soundness. A check at x=w*H shows why the canonical representative
bound is material. Another exercises noncoprime width/height2/2.

All four final direct `lake env lean -M6000 -j1` commands passed, with
fresh main objects in the repository object directory and checks
importing them. Both main logs are empty; four plus two axiom reports
contain only `propext`, `Classical.choice`, `Quot.sound`. Check log
SHA-256s: `a9e871964577517dae1cb0a8e31b413c5db4662a110329c1433a949cd70bd340`
and `b2010f5f022cd1bbec8a325ff6cb342f6cefafdbb8ecdbdbd46b6cc568fd4110`.
Existing prerequisites were reused, without a whole-closure replay
claim. Development corrections exposed false-if simplification,
explicit finite-index check arguments, zero-add normalization and
the standard ZMod value injectivity API; theorem premises were unchanged.

The [independent marker review](wang-tiles942-marker-construction-peer.md)
passed four isolated fresh builds, with unchanged31 pinned inputs and
byte-identical main objects. It found no additional premise or marker
assumption in either proof.
