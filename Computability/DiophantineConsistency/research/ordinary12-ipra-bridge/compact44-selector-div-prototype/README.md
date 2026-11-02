# Compact44 selector count and payload divisibility

`CompactSelectorDiv.selector_payload_divisible` proves in every `IΣ₁` model
that, for arbitrary model naturals `n,P`,

```
n < 2¹⁰  and  NoCarry(n + 2¹⁰P, 2⁵¹ − 2)
  imply  n ≤ 1  and  2⁴¹ ∣ P.
```

`NoCarry` is the existing internal bitwise predicate and powers are the
model's internal exponential. The proof combines the independently audited
selector-count lemma with a low-51-bit decomposition. It permits arbitrary
high payload and does not assume globally carry-free payload additions.
The theorem assumes the displayed no-carry relation and n bound; it does not
derive either from the graph.

The divisibility result supplies one prerequisite for the independently
packaged empty/selected copy arithmetic implications. It does not by itself
extract selector values, establish the required `W<2⁴¹` or payload-shape
cases, bind compact44 constants, simulate the machine, calibrate the checker,
prove existence of an iPRA proof, or establish consistency equivalence.
This is a conditional model-level result in classical Lean metatheory.

## Evidence

Exploratory session 74792 exited 1 on a local `2¹=2` rewrite; its exact
[source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained, and its `sorryAx` is not proof evidence. Corrected session 41482
[exited 0](observations/attempts.txt) with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) pins the independently audited selector-count
parent and matched seeds, rechecks the independently audited 24-module
window parent, and compiles this suffix over fresh author/peer overlays with
exact direct-import checks. It does not rebuild inherited chains; the window
parent audit has no complete axiom inventory, and Foundation outer-wrapper
and package-transitive/dynamic ancestry limitations remain. Resource sampling
is not a continuous whole-process-tree hard quota.

Outer session 42410 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `784ad1bd572ca6da2d457dd2e7a726650af9eae767ff55ce5e153bf0ce2d0d37`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-compact-selector-div-pair-new
```
