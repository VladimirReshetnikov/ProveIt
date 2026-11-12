# Decimal selector seed to symbolic kernel: source-only route

This packet drafts a Lean route from the separate decimal-render candidate's
15,086-digit seed to its compact symbolic kernel, without expanding any of the
roughly 178,000-digit port values. All three `.lean.src` files are inert and
unelaborated. Their `#print axioms` commands have not run. The draft neither
proves seed equality nor imports or proves the natural-79 endpoint.

`PrintedDecimalSeed` is the exact decimal numeral from the separate candidate.
`PrintedDecimalBlocks` is its 943 little-endian blocks, each less than
`10^16`. `DecimalSelectorKernel` proposes:

* a closed `symbolicSeed` obtained from the 943 `Compact943Data.row` selector
  values via `Nat.ofDigits (10^16)`;
* a uniform selector bound and the block-recovery theorem using the existing
  `SparseRadix.digit_ofDigits` declaration;
* a general `decimalKernel_of_blocks` proof by equality of finite sums,
  identifying the displayed K formula with `paramKernel r` whenever each
  block is the corresponding selector; and
* a low-mask formula whose proposed equality to `lowNat` directly uses
  `CompactConcreteMask.concrete_recipe`.

The critical closed Lean identity remains **unproved**. The conditional
`seed_equality_of_finite_checks` separates it into two explicit obligations:

1. `printedSeed = Nat.ofDigits (10^16) printedBlocks`;
2. `printedBlocks = selectorBlocks`.

If both were Lean-checked, the proposed general declarations would yield the
printed K identity. A practical implementation could split the 943-element
comparison into independently checked chunks, assemble the list equality,
and use the existing radix lemmas for packing. No resource or kernel-check
success is claimed for a 15,086-digit Lean numeral, a large `decide` proof, or
this tactic source. The four-port bridge separately needs the beta identity
and the displayed shifted-high formula's equality with `betaNat + highNat`.
The latter has related existing byte-reconstruction theorems but is not
proved here. The graph-syntax and endpoint binding also remain separate.

`check_source.py` pins the draft and relevant selector/radix source files. It
checks externally that the numeral is exactly the candidate's decimal seed,
that each printed block equals the corresponding Python transcription of the
pinned selector source, and that concatenating the blocks reconstructs the
seed. This is useful finite evidence, not a Lean proof or authentication of
TeX/PDF semantics. `SparseRadix.digit_ofDigits` and
`CompactConcreteMask.concrete_recipe` are existing source declarations whose
own provider/proof ancestry must be checked in the eventual environment.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-selector-kernel-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-selector-kernel-draft/result.json
```
