# Independent review: actual Wang language completeness

Verdict: **PASS**, with no requested source corrections. Reviewer:
`circuit_reduction`, independent of `complemented47_review`, who authored
CycleBand and Completeness. This review discloses that the reviewer authored
the imported TraceCycle, CycleBoundary, Periodic, and several earlier literal
language/row-construction packets. It is an independent review of the new
composition, not an independent reimplementation of every dependency.

The four complete sources, both author receipts, the full Soundness and
DecimalMachineZFC modules, and the exact `MarkedWord`, `BlankHalts`, and
`DiophantineConsistency.ConZFC` definitions were read. HelicalExtension and
HelicalQuotient had also been fully read in this review session before the
BandMarker construction. The four frozen sources were freshly replayed in
sequence against an isolated object overlay; no reviewed source was edited.

## Frozen bindings

Source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `WangTiles942CycleBand.lean` | 167 | `feff6383911a22e0f496f95eff693d0ee757861831890f555cf85c5370de18e8` |
| `WangTiles942CycleBandChecks.lean` | 82 | `adbc833379205c7784de10393dbe682654812d8962f7523aa26ef6ab639b1091` |
| `WangTiles942Completeness.lean` | 81 | `fcddd37eb2cec2e11c6845226839c0ea557d9edd17175d1c60d7b4f46ec21615` |
| `WangTiles942CompletenessChecks.lean` | 60 | `23f26e9fe078824c49936a2070a0d4a4eb38f319a1981053974cc5ccb239864c` |

All four source hashes were checked before and after their replay and stayed
unchanged. Important composition dependencies are pinned as follows:

| Dependency | SHA256 |
| --- | --- |
| `WangTiles942TraceCycle.lean` | `58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e` |
| `WangTiles942CycleBoundary.lean` | `a2f992dbfd4c14d70b8daf423c0b598d714131c5605cf29c833bc7dc2b808f8f` |
| `WangTiles942HelicalExtension.lean` | `1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6` |
| `WangTiles942HelicalQuotient.lean` | `dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481` |
| `WangTiles942Periodic.lean` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |
| `WangTiles942Soundness.lean` | `7380edb40832cc974606eddd2651b9b765712ac9bdb55cdb1ae1e7a83d450068` |
| `DecimalMachineZFC.lean` | `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107` |
| `Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |

## Mathematical and binding review

The band places one seam at x=-L and uses the actual trace cycle elsewhere.
The seam is an actual Allowed constructor with west equal to the square of
the previous row's edge code and east equal to the current code. At row0 this
is `(1,437,2,437)`; at row1 it is `(4,437,0,437)`. The order matters. The checks
explicitly reject replacing the previous squared code with the current one.

Signed time is reduced with `ZMod H`; its successor agrees with the cycle's
modular `nextIndex`. Thus the temporal proof covers reset-to-initializer and
negative times. The initializer replaces only run-row0, whose output already
agrees with the actual run1 initialization. Height at least3 separates the
initializer, finish, and reset roles. Actual halt atT and T+2≤H make the
finish configuration halted; the run-row boundary proof uses actual heads at
both t and t+1, not a supplied clean-row assumption.

The horizontal seam equations have the correct helical orientation:
`band(-L,t+1).west = band(R-1,t).east`. Together with interior matching, they
supply exactly the extension's boundary premise. The interval is half-open
[-L,R), so the right seam is supplied by the next copy rather than duplicated
inside the canonical band. Its extension has periods `(L+R,-1)` and `(0,H)`.
The quotient uses the same signed address `-x-(L+R)*t` as `MarkedWord`.
`marked_word_of_halt` retains every original-band tile for all integer times.

The construction has precisely these substantive hypotheses: an actual halt
of `DecimalMachine215.machine.run T`, T+2≤L, T+2≤R, T+2≤H, and 3≤H. No
boundary-cleanliness, independently supplied run, normalization, uniqueStart,
coprimality, or tiling/machine-equivalence premise is hidden in the statement
or in the immediate composition. The derived width and modulus are positive.

`cofinal_marked_word` is genuinely independent in width and height: for every
w≥2T+4 and H≥max(T+2,3), set L=T+2 and R=w-L. `width_split` proves both the
right-margin bound and L+R=w before the dependent modulus is substituted.
There is no divisibility restriction. This is a sufficient cofinal range,
not a claim that these bounds are minimal.

`ExistsMarked` quantifies positiveN, an arbitrary integer stride, and an
actual indexed word `ZMod N → Fin942` with exactly the existing three
MarkedWord fields. It assumes neither uniqueStart nor a rectangular shape.
The forward construction chooses w=2T+4 and H=T+3. The reverse direction
passes the same supplied word directly to `Soundness.marked_blank_halts`.
That dependency derives an actual blank halt before the vertical period:
otherwise its literal row-step induction reaches a configuration color≤433
at the periodic Start north435. No separate run correspondence is supplied.

The consistency corollary uses the unchanged definition
`DiophantineConsistency.ConZFC := ¬ BProv ZFCax_s [] Form.fBot`, not a new or
assumed consistency predicate. `not_congr` composes the literal blank-halting
equivalence with the existing closed decimal-machine endpoint. Consequently
this packet proves external Lean equivalences between the actual marked
language, actual blank halting, and the existing syntactic consistency
predicate. It does **not** assert consistency or nonhalting unconditionally,
formalize the implication internally in ZFC, or construct the remaining
Diophantine converse witnesses. The source and author receipts state this
scope correctly.

## Fresh isolated replay

A temporary overlay was placed first in `LEAN_PATH`. Its namespace contains
symlinks to unchanged prerequisite bundles, excluding the four reviewed
module bundles; those four were generated freshly and sequentially. Thus
CycleBandChecks and Completeness imported the freshly replayed CycleBand,
and CompletenessChecks imported the freshly replayed Completeness. No shared
object, cache, or source was overwritten. Existing prerequisite objects were
reused; this is not a fresh replay claim for the entire machine closure.

Each command, under the existing `lake env`, had this form:

```sh
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lean -M6000 -j1 \
  -o /tmp/wang-native-completeness-peer-4a1qb81e/DiophantineConsistency/MODULE.olean \
  /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/MODULE.lean
```

| Module | Result | Seconds | PeakKiB | Fresh object SHA256 |
| --- | --- | ---: | ---: | --- |
| CycleBand | PASS | 3.62 | 3210248 | `a8d9eeadb8ca5fceff82723c794952f0793fc024934741a8e0a14dab00c6d9e7` |
| CycleBandChecks | PASS | 3.01 | 3191848 | `87232ae0329af9f1f54f2748348781bee769ebeaf0e39baa08c03637a9a98f04` |
| Completeness | PASS | 3.66 | 3262900 | `5060667a543b53f66876197038fd82f1125a56cefe1c67b56086b66b9284f280` |
| CompletenessChecks | PASS | 3.00 | 3258544 | `b40be299c5ecaa9d116caf048070993f6ab076b4239ee3043db508f5174aa9a5` |

All four objects are byte-identical to the frozen author's shared objects.
Both main logs contain no Lean diagnostics. The15 CycleBand and7 Completeness
axiom reports contain only subsets of `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, or `native_decide` occurs in these sources.

An initial overlay setup omitted prerequisite namespace symlinks, so Lean
stopped immediately at a missing CycleBoundary object before checking code.
The corrected overlay replay above passed without any source changes. This
was an isolated replay-path issue, not a failed proof or dependency rebuild.

The complete command/source/output receipt is
`/tmp/wang-native-completeness-peer-4a1qb81e/REPLAY.json`, SHA256
`e95fd20e08c411171f86bb9fb8bd7f8aaa5e7efa564f393f17c5e42d4f8e2157`.
Log SHA256s, in the same directory:

- `WangTiles942CycleBand.log`: `343127bcb86e433ba7c6b5df0353c8de9dbbc8213317d014f90ff531cc95ef89`.
- `WangTiles942CycleBandChecks.log`: `a5b576c2ab12c00722ea76d0209cabd0b78a65a8dab1eb331c6e588b44287d1a`.
- `WangTiles942Completeness.log`: `98ae69a5002b1db5a58ffb464a819152c571bd061f9add1cfd6a48c17edb9c9f`.
- `WangTiles942CompletenessChecks.log`: `68aaf4834c37e60e72520851f6821175b4837409a9fa0e2083efe2416ac67ad1`.

Only this new peer receipt was added to the repository by the review. No
frozen sources, author receipts, shared documentation, or git state changed.
