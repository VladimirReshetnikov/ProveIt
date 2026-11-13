# Finite-sum compact selector/copy local equivalence

`CompactDecoderIff.decode_iff` proves in every `IΣ₁` model, for an
**external finite** index type `ι`, model-valued selectors `fᵢ`, values `vᵢ`,
and model natural W, that the following are equivalent:

```
NoCarry(n + 2¹⁰P, 2⁵¹ − 2),

(all fᵢ = 0 and W = 0) or
(exactly one fᵢ = 1, all others are 0, and W = vᵢ),

where n = ∑ᵢ fᵢ and P = ∑ᵢ (2⁴¹ − vᵢ)fᵢ + W.
```

Both directions are proved under the explicit assumptions `n < 2¹⁰`,
`W < 2⁴¹`, and `0 < vᵢ < 2⁴¹` for every index. Powers are the model's
internal exponentials and `NoCarry` is the existing internal bitwise
predicate. The reverse direction reduces the finite sums to the independently
verified mask values 0 and 1+2⁵¹; neither direction assumes that arbitrary
payload additions are globally carry-free.

This does not derive the assumptions from the 95-row graph, bind `ι` to the
actual 943-entry tile language or compact44 coefficients, simulate the
machine, calibrate the checker, prove existence of an iPRA proof, or
establish consistency equivalence. It is a conditional model-level result in
classical Lean metatheory, not an object-level iPRA theorem.

## Evidence

Exploratory author session 92826 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited forward-decoder and mask-converse parents,
checks their shared 24-module provider, validates the forward overlay's
three added seeds against its receipt, then compiles this join over fresh
author and peer overlays and checks direct imports. It does not rebuild the
inherited chains. The window parent audit has no complete axiom inventory,
and Foundation outer-wrapper and package-transitive/dynamic ancestry
limitations remain. Resource sampling is not a continuous whole-process-tree
hard quota.

Outer session 22578 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `7fdb96e86f0ac5503b68f616fd45591c5d299767e18896704ddbe7811319ad7d`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-decoder-iff-pair-new
```
