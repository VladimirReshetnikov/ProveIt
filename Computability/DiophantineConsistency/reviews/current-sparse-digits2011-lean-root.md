# Actual current zeros recover the Boolean supported selector word

Date: 2026-10-25. Author: circuit_reduction. Independent whole-source review
and fresh module/check replay: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentSparseDigits2011.lean | 5ce36d1cd28f0162e40d5e7ca712b0e77c7242a1ff9039016fc0765baf50b60d |
| CurrentSparseDigits2011Checks.lean | 86dc752aa1cdaa5317a8ed1986bfd742ea564abc506fbb8977c680a759069de9 |

ROOT read all140 module lines,58 check lines, the complete invoked generic
NativeRadixDigits and NativeVariableMask proofs, and the actual source-window
signature before execution. Both fresh commands exited0:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentSparseDigits2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSparseDigits2011.lean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSparseDigits2011Checks.lean
```

All five axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No new axiom or admitted proof occurs.

The new generic one-bit periodic-mask theorem proves the entire word equals
MC times the correct repunit plus one. It derives that final origin unit
rather than dropping it. The actual decoder therefore reconstructs the whole
word C, fixes its global origin digit to1, makes every supported coordinate
Boolean, and kills every excluded residue. This includes selector1, dummy977
and marker1004; the legacy two-bit dummy capacity is not used.

`polynomial_zero_reconstructs` begins with an actual positive zero of the
literal Current65 polynomial at the complete current masks and positive K.
The proved canonical-parent/source map supplies N>0, exact q and J, C>0,
C<q, and the actual low-mask test. No assignment word, digit bound, origin
bit or native interpretation is assumed by that endpoint.

The focused checks cover both support intervals and their holes, later-cell
repetition, the distinction between the global origin and other cell origins,
and the actual-MC counterexample showing why deleting the final+1 would
admit C=2 at the origin-mask level. They assert no false full polynomial zero.

ROOT independently reauthenticated every current source and final object in
the52-custom-module [dependency receipt](current-sparse-dependency-cache.json)
against the source-identical62ff checkout and checked toolchain/manifest
identity. Only two missing generic object bundles were reused; all50 existing
objects were preserved. This is not a fresh full ancestral or umbrella build.

The recovered origin bit is the Start selector bit. At-most-one selector
occupation per cell, phase/alignment recovery, tile/controller semantics,
the actual K recipe and internal-ZFC equivalence remain separate obligations.
