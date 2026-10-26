# Exact copy parity and South-word shifts

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. The author receipts are [copy parity](current-copy-parity2011-author.md)
and [South shifts](current-south-shift2011-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCopyParity2011.lean (200 lines) | dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a |
| CurrentCopyParity2011Checks.lean (67 lines) | b4c1cb086f9cb95e2cbb2cb061aa8830c3c68d93c3357f2d7875fb1314a75dcd |
| CurrentSouthShift2011.lean (162 lines) | 256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d |
| CurrentSouthShift2011Checks.lean (72 lines) | 5fda2aee996501ef7fd24fe6e10498aaf104a1b6846c641a53cfd938aab997e3 |

All four complete files were read before root execution. Each passed a
fresh direct `lake env lean -M6000 -j1` run. Main outputs went to separate
temporary objects; check runs used the author-built frozen import objects.
The main logs are empty. The nine copy-parity and seven South-shift axiom
reports contain only `propext`, `Classical.choice`, `Quot.sound`. This is
fresh verification of these sources, not their entire dependency closure
or the umbrella module.

Copy parity retains the full reflected convolution, actual masks, carry
recurrence and bounded-carry reset. At fields960+j, j<9, the bare18 source
is942+j. The other bare sources have residues1967+j and951+j and vanish
by the actual low support; the full cyclic coordinates are preserved.
The high mask forces evenness, the reflected sum is even and the incoming
carry is zero. Fractional phase zero makes the temporal digit Boolean,
so parity of the two Boolean digits gives their equality. Marker parity
is composed from its already checked literal binding. The explicit
count/phase hypotheses are discharged in the subsequent Facts composition.

The South-word module uses the exact cell translation equivalence, never
an assumed cellwise source. A generic binary-word split reconstructs
the nine-bit word at offsets19 and20. Their error bits are precisely
physical941, or940 and941 with weights1 and2. A two-entry subsum bound
on the same physical selector count bounds the latter error by2. The
focused checks compose the offset20 identity with the generic exclusion
of South510 without a decoded-label premise. The copy boundary check at969
retains its allowed spatial source and different mask.

No whole-field alignment, occupation, unique Start or all-marker-one
premise is hidden in these packets. Neither proves the machine-language
equivalence or the final Con(ZFC) theorem. The maintained decimal page
and equation metrics are unchanged.
