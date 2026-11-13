# Chunked proof proposal for the decimal selector seed

This packet proposes finite Lean declarations for the two outstanding
hypotheses in the separate [selector/kernel draft](../ordinary14-natural79-decimal-selector-kernel-draft/README.md).
All files in `source/` are inert `.lean.src` snapshots. **No Lean command has
run**, and neither `printedSeed = Nat.ofDigits (10^16) printedBlocks` nor
`printedBlocks = selectorBlocks` is proved by this packet.

The proposal partitions the 943 block indices into 29 consecutive chunks of
32 and one final chunk of 15. Each chunk states two exact finite comparisons
for every index in its range: the printed block equals its symbolic selector,
and it equals the corresponding base-`10^16` window of the literal printed
seed. The proposed proof is `decide`, with no claim that its elaboration,
kernel reduction, memory or time requirements are acceptable. Each module
includes a proposed axiom report.

The separate assembly source proposes to split an arbitrary index by these
intervals and then:

* derive `printedBlocks = selectorBlocks` by `List.ext_getElem`;
* use the existing `RadixWindowReconstruction.ofDigits_eq_of_windows`, the
  proposed block length and the proposed seed bound to derive the packing
  equality; and
* apply the previous packet's conditional `seed_equality_of_finite_checks`.

The 15,086-digit seed itself is not a 178,000-digit port expansion. Still,
each finite `decide` may need repeated evaluation of large numeral divisions
and list lookups. If 32-index chunks exceed the independently reviewed
resource limits or do not elaborate, split them further or use a proved
blockwise recurrence; neither success nor a particular performance profile is
assumed. Any future proof run needs its own source/provider and axiom checks.

`generate.py` pins the exact previous seed, block and selector source snapshots,
generates 30 chunk modules plus common and assembly modules in this directory,
and externally verifies all 943 selector values and all 943 exact decimal
windows. It does not change the previous packet. `check_source.py` is a
read-only independent coverage check of the generated files and repeats the
external integer controls. Its receipt verifies that the half-open intervals
cover `[0,943)` exactly once; it does not parse Lean or validate the proof
scripts. The arithmetic transcriptions, seed/page correspondence, physical
TeX/PDF semantics and endpoint derivability remain separate trust boundaries.

From the repository root, the following read-only check reproduces the receipt:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-seed-chunk-plan/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-seed-chunk-plan/result.json
```

`generate.py` regenerates only this packet's `source/` and `manifest.json`;
it does not invoke Lean or create any build output.
