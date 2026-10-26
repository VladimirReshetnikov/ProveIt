# Actual computation-band marker: author receipt

Status: frozen, freshly checked. Author: `circuit_reduction`. This is an author
receipt, not an independent peer review. Root authored the two marker helpers;
`complemented47_review` authored CycleBand. The present author previously wrote
the trace-cycle and cycle-boundary construction used by CycleBand.

## Frozen source binding

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/WangTiles942BandMarker.lean` | 124 | `4fe8030da31229c7758c9c1c4f73c1443fe1881875a34990adb8817fbf827cb4` |
| `Lean/DiophantineConsistency/WangTiles942BandMarkerChecks.lean` | 79 | `5bc5e508a7673cfc89f7b885336bfb375e90821c0c54b0d4e1735c00986a36a3` |
| `Lean/DiophantineConsistency/WangTiles942CycleBand.lean` | 167 | `feff6383911a22e0f496f95eff693d0ee757861831890f555cf85c5370de18e8` |
| `Lean/DiophantineConsistency/WangTiles942CycleMarker.lean` | 70 | `2806b219857cfc334bc502fc15eccbebf0f6206a381c2e809029905e7d9076c5` |
| `Lean/DiophantineConsistency/WangTiles942HelicalMarker.lean` | 60 | `55962b759130f61cb138afde6a87796da4a12ddf7b0bc891a2d2417da2c788c7` |

The last three are the complete direct imports, read in full before execution;
HelicalQuotient, HelicalExtension, and both new root marker check files were
also read. No dependency source or existing dependency object was modified.

## What is proved

`timeIndex_val_zero_iff` uses `ZMod.val_intCast` to identify finite cycle index
zero with the actual signed integer remainder `t % H = 0`. For `0 < L` and
`NeZero H`, `band_eq_start_iff` proves

```text
band L H x t = start  ↔  x = 0 ∧ t % (H : ℤ) = 0.
```

At the seam, north437 excludes Start's north435. Elsewhere, the exact
CycleMarker theorem supplies the coordinate classification. No halting,
height3, or matching premise is needed by this local marker statement.

`canonicalWord` is definitionally the existing `quotientWord` of
`extend (band L H) (L+R) L`, with allowedness discharged from the actual halt
and height bound. `canonicalWord_marker_iff` applies the actual helical
marker theorem and actual full-table tile injectivity. Its conclusion is
about literal indices: `canonicalWord ... z = 0 ↔ z = 0`.

`canonicalWord_properties` applies `quotientWord_marked` directly to this
same word, with the six extension properties discharged from CycleBand. It
also retains every original-band tile through `quotientWord_binding` and
`extend_on_band`. It does not choose a separate existential marked word.

`canonical_unique_word_of_halt` exposes the concrete word under internally
supplied nonzero-modulus instances. Its only substantive hypotheses are an
actual blank halt at timeT, `T+2 ≤ L`, `T+2 ≤ R`, `T+2 ≤ H`, and `3 ≤ H`.
The width and height may be independently enlarged; there is no coprimality,
unique-marker, clean-boundary, run-correspondence, or tiling assumption.

## Focused checks and limits

Checks verify negative time(-6) is an initialization period at height3,
negative time(-5) is not, and the seam never becomes Start. The L=0 negative
control proves why positive L is required: the seam replaces the origin.
Height1 still has the local marker property, without asserting temporal
validity. A definitional check binds the public word to the exact quotient;
a symbolic check derives nonzero indices away from the origin. A final
example varies both margins and the height independently by arbitrary
natural increments.

The construction assumes actual halting; it does not assert that this
machine halts, nor extend uniqueness to arbitrary marked words. This packet
does not yet construct arithmetic coefficient witnesses or prove their
bounds. Existing classical choice in `quotientWord` selects an actual tile
index; full tile injectivity ensures the claimed marker-index conclusion.

## Fresh validation

Full new main/check source was read before its execution. Commands ran
sequentially from the repository root with `Elab.async false` in source:

```sh
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942BandMarker.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942BandMarker.lean
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942BandMarkerChecks.lean
```

Both final commands exited0. Main:3.81seconds, peak3201176KiB, no Lean
diagnostics. Checks:4.10seconds, peak3169528KiB, exactly the five intended
axiom reports. All five report only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, new axiom, or `native_decide` was added.

The first checks run failed only in the L=0 negative control because a rewrite
changed both zero arguments into syntactically negated zero. Replacing it
with the explicit definitional seam equality fixed the check. Main source,
statements, and mathematical assumptions were unchanged; the complete final
checks file was reread before the successful replay.

| Output | SHA256 |
| --- | --- |
| `.lake/build/lib/lean/DiophantineConsistency/WangTiles942BandMarker.olean` | `d2ceea552bb1f2fd9470028d3952a2862319413f9a26b83714b315ca129261fd` |
| `/tmp/wang-band-marker-main.log` | `377bc076ea649dd2ba5a41b29ea8e15e88bb977f795030dabfb1583400d57ba2` |
| `/tmp/wang-band-marker-checks.log` | `cee5512508f75c9bb726ac0c166ad2e19edd2f2a19739185e93dbf4626f0970a` |

No frozen source, shared documentation, umbrella, or git state was edited by
this packet. The only new repository files are the module, checks, and this
receipt; the module's own object was freshly generated.
