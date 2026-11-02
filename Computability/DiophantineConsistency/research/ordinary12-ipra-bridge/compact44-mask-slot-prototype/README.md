# Conditional mixed-mask slot decoding

In every `IΣ₁` model, the three `CompactMaskSlot` theorems take an explicit
`NoCarry X M` hypothesis and an explicit equality for the radix digit
`dig 67 M k`. They derive the corresponding bound on `dig 67 X k`:

```
dig 67 M k = 2⁶⁷−1  →  dig 67 X k = 0,
dig 67 M k = 2⁶⁷−2  →  dig 67 X k ≤ 1,
dig 67 M k = 2⁶⁷−4  →  dig 67 X k ≤ 3.
```

Powers are the internal model exponential. The proof applies `noCarry_dig`
and the independently audited local mixed-width bounds; `dig_lt` supplies
the implicit radix-digit bound. In particular the third result does not
claim that a two-bit dummy is Boolean.

The mask-digit equality is **assumed**, not established for the compact44
MC. The theorem does not derive `NoCarry X M` from the graph, handle the
incremented origin of `(MC·J)+1`, prove a global carry bound or clean reset,
bind the full tuple, simulate the machine, calibrate its checker, or establish
an iPRA proof or consistency equivalence. These are conditional model-level
results in classical Lean metatheory.

## Evidence

Exploratory author session 93674 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited mixed-mask parent and matched seeds,
rechecks the independently audited 24-module window parent, then compiles
this suffix over fresh author and peer overlays and checks direct imports. It
does not rebuild inherited chains. The window parent audit has no complete
axiom inventory; Foundation outer-wrapper and package-transitive/dynamic
ancestry limitations remain. Resource sampling is not a continuous
whole-process-tree hard quota.

Outer session 10295 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `ddef69b4310caef263591491dafe50cc9e9d01542fcaecfb7479c9fa7a0704d9`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When pinned temporary parents remain available and
the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-mask-slot-pair-new
```
