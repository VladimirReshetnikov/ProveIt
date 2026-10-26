# Closed marked-language consistency endpoint and concrete unique marker

Date: 2026-10-26. ROOT independently read both complete frozen main/check
pairs and author receipts before four fresh capped Lean runs. Both main
builds and checks passed. Fresh main outputs were separate `/tmp` objects;
checks imported frozen author objects. Existing dependency objects were
reused; no complete arithmetic/machine closure rebuild is claimed.
ROOT authored imported Soundness and marker helpers; this review concerns
the other agents' new compositions, without independent-authorship claims
for those earlier prerequisites.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Completeness.lean (81 lines) | fcddd37eb2cec2e11c6845226839c0ea557d9edd17175d1c60d7b4f46ec21615 |
| WangTiles942CompletenessChecks.lean (60 lines) | 23f26e9fe078824c49936a2070a0d4a4eb38f319a1981053974cc5ccb239864c |
| WangTiles942BandMarker.lean (124 lines) | 4fe8030da31229c7758c9c1c4f73c1443fe1881875a34990adb8817fbf827cb4 |
| WangTiles942BandMarkerChecks.lean (79 lines) | 5bc5e508a7673cfc89f7b885336bfb375e90821c0c54b0d4e1735c00986a36a3 |

For an actual halt atT, `cofinal_marked_word` chooses left marginT+2
and gives all remaining width to the right. The exact inequalities
w≥2*T+4, H≥T+2 andH≥3 suffice independently. The width equality is
proved before substituting dependent finite types. The result is an
actual word on `ZMod(w*H)` with stridew, without coprimality or extra
clean-run assumptions.

`ExistsMarked` carries a positive natural modulus, arbitrary signed
stride, actual `Fin942` tile indices and the unchanged `MarkedWord`
predicate. `existsMarked_iff_blank_halts` proves both directions for
the literal decimal machine: construction uses width2*T+4,heightT+3;
soundness uses the previously proved actual halt before the word's
vertical period. Composing the exact existing machine endpoint gives
`no_marked_word_iff_conZFC : (¬ ExistsMarked) ↔ ConZFC`. This is a
closed external Lean equivalence for the actual finite language.

The marker packet proves the actual band's local classification:
Start iff x=0 and t%H=0. The seam's north437 excludes Start; interior
classification follows from the proved cycle marker and signed finite
time value. Positivity of L is material, since atL=0 the seam replaces
the origin. The local classification needs no halt or height3 premise.

`canonicalWord` is definitionally the actual quotient of the extended
band, with allowedness discharged from halt and height. Its marker is
unique as a literal index: a(z)=0 iff z=0. Full table injectivity moves
from tile values to indices. `canonical_unique_word_of_halt` proves
that this same concrete word is marked, uniquely marked and preserves
every canonical-band tile. Independent T+2≤L,R,H andH≥3 are the only
substantive inputs besides the actual halt; uniqueness is derived.

Checks retain failed minimum-width allocation, the separate height3
guard, noncoprime dimensions, arbitrary independent padding, signed
negative times, the L=0 negative control and exact quotient identity.
No actual halt or consistency is asserted unconditionally.

All four root runs used `lake env lean -M6000 -j1`. Both main logs are
empty and all seven plus five axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`. See author receipts for
[completeness](wang-tiles942-completeness-author.md) and
[the concrete marker](wang-tiles942-band-marker-author.md).
The root check log SHA-256s are
`ca62ce4d174f6be1604423417763abf28a28e7a8c21130bdc5c854a94bd6d41f`
and `b176e69e3aa4f9ab900b2350b7112c3d61da7b0b595c327cedd5047066ab66ad`.

The equation's reverse direction still requires constructing the
global Boolean coefficient word, its cyclic carries, the composite
rank controller and positive Pell/arithmetic witnesses. This native
language endpoint is not the full Diophantine equivalence. Remaining
frontier equations and the internal-ZFC derivation also remain open.
The displayed decimal equation and all size metrics are unchanged.
