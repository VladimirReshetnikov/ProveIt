# Low-mask safety at every packed-word slot

`CompactWordLowSlot.lean` transfers the checked base and single-pulse
low-mask safety of each valid compact cell to the actual represented packed
word. For Σ₁-definable row and dummy functions, a supplied
`CompactWord row N s` and Boolean dummy values, it proves

```
∀ k < 8807*N,
  NoCarry (dig 67 (packedWord row dummy N) k)
          (dig 67 lowNat (k % 8807)).
```

The statement includes slot zero and identifies the exact symbolic
`lowNat` by the previously checked mask equality. It uses quotient/remainder
to select the containing cell, the represented packed-digit identity and
`noCarry_dig`. No `PackingInput`, pulse support, high-mask or graph-zero
premise is needed. This supplies the low-slot hypothesis used by the
existing field-window column lemmas; it does not by itself prove high-mask
safety, a graph zero or an internal iPRA theorem.

The bounded single-author run, tool session `17278`, exited 0 without
warnings or `sorryAx`; both named axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. Direct dependency guards, the full
selected project union overlay and selected controller, symbolic-kernel and
static-mask root inventories were unchanged. Provider-overlap comparisons,
selected inventories, source/object hashes, command, dependency list, log
and terminal receipt are retained in `observations/attempt01`.

This is a mixed-provider author-side build, not a paired replay or a fully
authenticated dependency closure. Package, transitive, dynamic-loading and
between-observation ancestry remain inherited.
