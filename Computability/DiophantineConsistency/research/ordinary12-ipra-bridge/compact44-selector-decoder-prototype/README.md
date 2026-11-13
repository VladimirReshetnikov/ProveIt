# Finite-sum compact selector/copy decoder

`CompactSelectorDecoder.decode` works in every model of `IΣ₁`, for any
**external finite** index type `ι`, model-valued selectors `fᵢ`, values `vᵢ`,
and model natural `W`. Put

```
n = ∑ᵢ fᵢ,    P = ∑ᵢ (2⁴¹ − vᵢ) fᵢ + W.
```

Under the explicit hypotheses

```
n < 2¹⁰,
W < 2⁴¹,
for every i, 0 < vᵢ < 2⁴¹,
NoCarry(n + 2¹⁰P, 2⁵¹ − 2),
```

it proves either every selector and W is zero, or there is exactly one
selector equal to 1, all other selectors are zero, and W is its value. The
powers are internal model exponentials; `NoCarry` is the existing internal
bitwise predicate. The proof derives the empty and selected payload shapes
from the actual finite sums, uses the no-carry-derived 2⁴¹ divisibility, and
applies the separately audited empty/copy arithmetic. It does not assume
that payload additions are globally carry-free.

The theorem does not derive its input hypotheses from the 95-row equation,
bind `ι` to the actual 943-entry tile language or the compact44 coefficients,
prove the full decoder converse, simulate the machine, calibrate the checker,
prove existence of an iPRA proof, or establish consistency equivalence. It is
a conditional model-level result in classical Lean metatheory.

## Evidence

Exploratory author session 4526 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the three independently audited divisibility, copy and finite-sum
parents and their matched seeds, checks the shared 24-module window provider
and the selector-divisibility overlay's exact added selector seed, then
compiles the join over fresh author and peer overlays. It verifies direct
imports and matching outputs; it does not rebuild the inherited chains. The
window parent audit has no complete axiom inventory, and Foundation
outer-wrapper and package-transitive/dynamic ancestry limitations remain.
Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 63674 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `6089c57318e1156c0b110185ec535d65e4193739575441fc168248c587524180`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-selector-decoder-pair-new
```
