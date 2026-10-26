# Independent review: CurrentWordOrigin2011

PASS. I independently read all 118 lines of root's main module and all 54 lines of its checks, checked the relevant imported definitions and proofs, and freshly replayed both in isolation. No correction is requested. This is independent review of root's new origin composition; I authored its earlier word, cell, clause, kernel, and TopBounds dependencies, so I do not claim independent authorship or review of those prerequisites here. The separate Copies and mask bindings were also inspected in full where used. No frozen source or shared object was changed.

## Exact bindings

| File under `Lean/DiophantineConsistency/` | Lines / bytes | SHA256 |
| --- | ---: | --- |
| `CurrentWordOrigin2011.lean` | 118 / 5454 | `6b6bb89e40422745154e5ef990d9909a65b740d43e86842b54fde887f5de3f56` |
| `CurrentWordOrigin2011Checks.lean` | 54 / 2516 | `141e38f2420bb0b6aa29f3e42fdb294944a9edd7eca3dc5ae9d6d8d37108e558` |

The main imports frozen `CurrentWordCopies2011` and `CurrentWordTopBounds2011`. I read the complete Copies source, the actual `MarkedWord` definition and orientation, the full high-mask digit module, and the invoked source support, local Start, whole-cell shift, low reset, and preceding-top reset interfaces. I also read the subsequently completed root author receipt `reviews/current-word-origin2011-lean-root.md`, SHA256 `b99d692a26dd94468241221a689826528fdf9a92f17ae1e94547fb477c728e3d`; its stated scope and source/object bindings agree with this review. It was received after the isolated replay, so it is not counted among the 29 before/after inputs.

## Mathematical review

At any aligned origin the three bare input residues are 1993, 1007, and 2002, all above the actual source support maximum 1004. For every reflected entry, the exact identity moves its source to field `1006+position e` of the preceding cell. Since `0≤position e≤985`, that entire interval is unsupported and remains below 2011. Consequently the complete actual folded convolution is zero. These identities allow arbitrary numeric dummy and marker maps; Boolean controls are introduced only for the carry statements.

For the constructed canonical marker, the outgoing origin carry is derived from the actual low reset. The incoming carry is separately derived from field 2010 of cell `j-1`, with the exact equality `base(j-1)+2010=base(j)-1`. Thus no clean-boundary premise is supplied or silently borrowed from the interior low-band argument. These cyclic identities cover the last/first cell and `N=1`.

The actual binary rotation at whole displacement `47*(2011*s)` reduces to subtraction of `2011*s`. `word_shift_at_base` then gives the local Start bit of `a(j-s)`. The normalized origin digit is therefore precisely `if a(j-s)=0 then 1 else 0`. The sign is the actual temporal direction; no restriction on s or its size relative to N is introduced.

For the global origin, `MarkedWord.temporal 0` and `start_at_zero` imply that `a(-s)` cannot also be Start: the contrary would equate Start's south color 1 with its north color 435. This is a local predecessor exclusion, not a globally unique-Start assumption. It forces the global normalized digit to zero, hence passes the actual exceptional mask 3. Every other aligned origin has mask 4, which permits either derived digit 0 or 1. The proof uses actual `maskDigits`, not an invented uniform origin mask.

The checks explicitly preserve numeric-control convolution absence at `N=1`, the possibility of a non-global origin digit 1, the distinction `1 &&& 4=0` versus `1 &&& 3≠0`, and the impossibility of actual marked words at stride zero or `N=1`. The final check constructs its normalization via the existing carry endpoint and then proves every origin test; it does not assume the test, clean carries, unique Start, or a machine run.

This packet establishes only the family of cell-origin high-mask tests. It does not by itself assert all high-mask fields, a full source-system solution, the controller arithmetic, or polynomial completeness.

## Fresh isolated validation

After the full source reads, I prepared `/tmp/current-word-origin2011-controller-peer` with both reviewed stems absent. Other required project objects were symlinked unchanged; the temporary path was prepended to the existing Lean path. The main was compiled first into the overlay, then the checks imported that fresh main. Both commands used Lean 4.32.0, `-M6000 -j1`, and the source's `Elab.async false`; neither command rebuilt the prerequisite closure.

- Main: exit 0, 3.70 seconds, peak 3272420 KB; no Lean diagnostics.
- Checks: exit 0, 2.69 seconds, peak 3254440 KB; six axiom reports, all limited to `propext`, `Classical.choice`, and `Quot.sound`, without warnings.

Both fresh objects are byte-identical to the frozen root objects:

- Main object: `5533a1a5815948582be193d9ae0b3a62a8e9f20425ed9402b1f18d99f8ca32a1`.
- Checks object: `28ada5474edf83bb2cfc28c08b6fadb242181889c4885e712562f041abb157d9`.

All 29 selected source/object/toolchain inputs remained unchanged across the replay. The manifest SHA256 is `7e08fdbc22aad80386ad6d0ddf05814d697aefa1a1daf9f3c3fe34b659ada0b5`. Logs including timing are `/tmp/current-word-origin2011-controller-peer/main.log`, SHA256 `59751e1abc46318c7b9e171985b5f1c1da9855e8331386bbe5f744ced9bddc92`, and `checks.log`, SHA256 `6b76f2d1d6885e379220430a28b9c591516e2d716e1ca5f173d11454011678e3`. No full fresh dependency replay is claimed.
