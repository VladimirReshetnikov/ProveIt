# Conditional free-J radix alignment

`FreeJRadixAlignment.graph_alignment` works in an arbitrary model of `IΣ₁`
under the same assumptions as its independently audited cancellation parent:
the actual 95-row free-J literal has an internal zero at twelve positive
coordinates; β > 0, MC < β and MF < 2β; additionally β ≥ 46, d ≥ 4, and the
model port equation β = 2ᵈ−1. It constructs model naturals `N,w` with

```
N > 0,  q = 2^(dN),  dN ≤ R,  w = 2^(R−dN),  v₅ = q w,
q = 1 + v₀β,
R = ((q−1)(q−v₁)+v₂)(q²−1)+(MC+q MF)v₀.
```

The powers are the model's internal exponential. The result combines
`q ∣ 2ᴿ` and `v₅=2ᴿ` with the existing model `factor_alignment` theorem;
N and w are proof coordinates, not new equation variables. It does not
interpret the chosen compact44 constant, calibrate the associated checker,
prove existence of a proof in iPRA, or establish the final consistency
equivalence. It is a conditional model-level result in classical Lean
metatheory.

## Evidence

Exploratory author session 20084 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited cancellation parent and matched seed objects
and inherited chains, then compiles this source over fresh author and peer
overlays and checks direct imports. It does not rebuild inherited chains.
The graph parent's manifest-at-read qualification and Foundation outer-wrapper
and package-transitive/dynamic ancestry limitations remain; resource sampling
is not a continuous whole-process-tree hard quota.

Outer session 55579 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `47032d5f0cca7c2aa42ccf5247ddccee06d2b238a9856b2aac664a62717fe998`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-radix-align-new
```
