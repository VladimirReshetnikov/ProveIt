# Exact first-carrier quotient for the free-J graph

`FreeJExactTransport.first_quotient` works in an arbitrary model of `IΣ₁`
under the same exact 95-row free-J internal-zero, positive-coordinate, and
port assumptions as its independently audited exact-index parent: β > 0,
MC < β, and MF < 2β in the model. It proves the existence of a model natural
`t` such that

```
k = R + 1 + 4Qt,
k = v₈ + v₉,  Q = (v₅v₆)v₆,
q = 1 + v₀β,
R = ((q − 1)(q − v₁) + v₂)(q² − 1) + (MC + q MF)v₀.
```

It uses the exact first index j satisfying 2j = R + 1 and the existing
`first_transport` theorem; the witness is a proof coordinate, not an added
equation variable. In particular this does not assert that the separate
ordinary exponent indexing f equals R, or assume Δ divides the multiplier.

This is a conditional model-level theorem using classical Lean metatheory.
It does not establish the compact44 port interpretation, checker
calibration, an iPRA proof, or the final consistency equivalence.

## Evidence

Exploratory author session 4733 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited exact-index parent and both matched seed
objects and inherited chains, then compiles the source over fresh author and
peer overlays and checks exact direct imports. It does not rebuild the
inherited chains. The graph parent's manifest-at-read qualification and the
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain. Resource sampling is not a continuous whole-process-tree hard quota.

Outer session 97245 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `e7788aa4e57a2cb0f4c3ad13da09ff2653def41ed4c8cf89f925d2cba26b8cf7`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; the [author](evidence/author.log) and
[peer](evidence/peer.log) reports contain only `propext`, `Classical.choice`
and `Quot.sound`, with no warnings or `sorryAx`. Independent review of this
new suffix remains required. When the pinned temporary parents remain
available and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-exact-transport-new
```
