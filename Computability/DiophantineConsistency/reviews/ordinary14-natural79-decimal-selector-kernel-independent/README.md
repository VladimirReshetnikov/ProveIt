# Independent review: decimal selector and kernel draft

The revised [selector-kernel source proposal](../../research/ordinary14-natural79-decimal-selector-kernel-draft/README.md)
and this independent checker reproduce. The finite decimal data, selector
ordering and source-level argument interfaces match the intended route. This
is an external arithmetic and source review, not Lean elaboration, proof
certificate, or provider authentication.

The checker reads the exact 15,086-digit proposed Lean numeral and recovers
943 blocks by repeated integer division by `10^16`, independently of the
author's concatenation check. All blocks match the proposed least-significant-
first list and the selector formula computed from the 943 ordered source rows.
The printed decimal integer has two leading zero digits when viewed as 943
16-digit blocks. All row values are below `2^41`, so the external integer
subtraction matches Lean's natural subtraction for this fixed table.

The proposed uniform selector bound needs no table case split: for any natural
`v`, `2^41 - v ≤ 2^41` under natural subtraction, hence the selector is at
most `1 + 2^51 = 2,251,799,813,685,249 < 10^16`. The inspected
`SparseRadix.digit_ofDigits` source requires a positive radix, every list
element below it and an in-range index, then returns the corresponding
least-significant-first list element. The draft supplies those interfaces with
`selectorBlocks_bounded` and the length proof, and its intended result agrees
with `List.ofFn` selector indexing. Actual tactic simplification, imports and
instance/name resolution remain untested.

The kernel identity is **conditional** on recovering every selector block.
The closed printed-seed identity is not proved: the draft explicitly assumes
both `hpack : printedSeed = Nat.ofDigits (10^16) printedBlocks` and
`hblocks : printedBlocks = selectorBlocks`, and the printed-kernel theorem in
turn assumes `hseed`. The external calculations here do not discharge these
Lean premises. The proposed K formula uses the same sums as the symbolic
kernel and the power identity `r^8849 = r^8807*r^42`; its low-port theorem
invokes the existing source declaration `CompactConcreteMask.concrete_recipe`.

During review, the initial source's `rw [hpack, hblocks]` followed by `rfl`
was identified as a potential no-goals tactic error: the toolchain's `rw`
macro tries reducible reflexivity after rewriting, and `symbolicSeed` is a
reducible definition. The author replaced it with the explicit transitivity
and `congrArg` term before this receipt was pinned. This source-level repair
has not been tested by Lean. The 943-block obligations, digit literal parsing,
proof-resource budget, selected imports/providers, all seven `#print axioms`
commands, and the endpoint/TeX/PDF bindings remain open.

From the repository root with the pinned Lean toolchain source available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-selector-kernel-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-decimal-selector-kernel-draft/result.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-selector-kernel-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-selector-kernel-independent/result.json
```
