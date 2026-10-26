# Constructed top fields and strict bounds: independent Lean review

Date: 2026-10-26. Reviewer: `circuit_reduction`. Author: `controller_certificate`.
Verdict: PASS; no requested source changes.

## Sources and review scope

I read the entire259-line main,85-line checks and full author receipt before
execution, then confirmed both announced frozen hashes. I checked the exact
kernel exponent and support definitions, the existing source-position
injectivity and doubled-weight bound, the current word and carry interfaces,
and the ordinary top-field/bound argument. I authored the older reflected
geometry, copy and periodic modules; I did not author this reviewed top-field
packet, its clause prerequisite, kernel, or assembled word. That prerequisite
authorship is disclosed rather than claiming independence from the entire
construction chain.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentWordTopBounds2011.lean` | `7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f` |
| `Lean/DiophantineConsistency/CurrentWordTopBounds2011Checks.lean` | `d90115c218fc12fc7f9667089392bafb4e7777cc7452f9422544fdf8065d4b20` |
| Sole direct import `CurrentWordClause2011` | `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc` |
| `reviews/current-word-top-bounds2011-author.md` | `2af4986a8fbf7e6829a2a9d39e4c4e12df0141357f3064ce07410e03fb4e23d1` |

Paths are relative to `Computability/DiophantineConsistency/` unless absolute.
Existing prerequisite objects were reused. This is a fresh replay of the two
new sources, not a replay of the complete prerequisite closure.

## Exact arithmetic findings

At output2009, each reflected source is exactly1004+position(e). The existing
position injection and physicalPosition(Start)=0 prove that only the actual
Start coefficient survives, giving `2*weight(inl 0)*marker j`. Every other
reflected source lies between1005 and1989, where the actual word is zero.
No source-array order is guessed. The three bare inputs have unsupported local
residues, including the spatial input wrapped into the preceding cell. The
identity correctly retains an arbitrary numeric marker rather than silently
bounding it by1.

At2010 every reflected source is at least1005; its three bare sources are again
unsupported. Thus the whole kernel convolution is zero. Under the specified
whole-cell displacement, the temporal inputs at both top fields also vanish
because their local residue is unchanged. This works across complete periods
and at N=1; no assumption that the cyclic positions are distinct is needed.

With Boolean controls, the actual sole coefficient at2009 is below2^45, so
adding the existing incoming carry bound57 is below the radix2^47. The carry
recurrence therefore resets2009. The zero raw field2010 then gives both zero
outgoing carry and zero digit. These statements concern every bounded
normalization supplied by the actual construction, with no high-mask, tile
matching or controller premise.

The generic prefix lemma reindexes the full ZMod word by its canonical natural
range and removes an explicitly proved zero suffix. It includes L=0. The final
cell's top field is proved to have exact representative N*2011−1, including N=1.
Consequently F is strictly below radix^(N*2011−1), and positive N justifies the
exact division identity with q/radix. This is a bound on the same normalized
word, not an unrelated residue representative.

The source exponent N*2011−1006 is correct: the last possible nonzero source
position is (N−1)*2011+1004, and the exclusive prefix length is that value plus1,
namely N*2011−1006. The proof uses only actual periodic support and Boolean
source digits. At N=1 it becomes C<radix^1005. It is independent of temporal
stride, carries, matching and masks.

The final existential check constructs the same carries/digits through the
clause endpoint, retains its positive F, and proves the top zero, stronger F
bound and source bound together. There is no desired strict-F premise hidden
in that composition. Whole high-mask acceptance, origin tests, rank correction
and equation completeness remain outside this packet.

## Fresh isolated replay and checks

Using the pinned `lake env`, I placed the temporary overlay
`/tmp/current-word-top-bounds-peer-b1jx3ssu/` first in LEAN_PATH and symlinked
unchanged prerequisite bundles into it. I excluded both reviewed objects from
those links and compiled them freshly and sequentially with `lean -M6000 -j1`;
the checks imported the new main object. Both sources set `Elab.async false`.
No shared object or dependency bundle was overwritten.

Both commands exited zero. Main elapsed5.47s, peak3290488KiB, with no Lean
diagnostics. Checks elapsed2.82s, peak3252280KiB. The checks reproduce the author's
benign warning that exponent1005 exceeds the evaluator threshold256; the term
is retained symbolically and the proof succeeds. I do not claim an empty checks
log. All16 axiom reports contain only `propext`, `Classical.choice`, and/or
`Quot.sound`. The reviewed sources contain no `sorry`, `admit`, new axiom, or
`native_decide`. Source hashes were unchanged, and both new objects are
byte-identical to the author's shared objects.

Focused checks cover an empty prefix, maximal lower digits, a nonzero-suffix
negative control, exact top indices at N=1 and N=2, raw identities with numeric
controls17/23, seventeen whole periods at N=1, the separate source bound, and
all stronger conclusions for an actually constructed normalization.

| Replay output | SHA-256 |
| --- | --- |
| Main `.olean` | `e9a8ad9d137e9493351a846ea4946714f6d0a3878b2e39a596ae30334df911ac` |
| Checks `.olean` | `80dbaaaeded2c8d6e071031c0816044747778e0af1c63f6c3c7cebfb97e92fcc` |
| Main log | `e98967759134ae2401d82a09b1d55abeacc3c5ff9d9e86d8a06ac12536cc352e` |
| Checks log | `d1e8e25ddc4a0e9e8c8cc033dab09334d5b4c1778e73dc73cbed1aad33905241` |
| `REPLAY.json` | `8506ca23a0ef2020bca4fc1d1d827be34920243d108a8edf4d024a3f067ff4e3` |

Only this new peer receipt was written. No frozen source, shared status document,
or git state was edited.
