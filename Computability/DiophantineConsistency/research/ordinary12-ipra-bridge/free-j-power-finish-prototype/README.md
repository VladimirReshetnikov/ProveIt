# Exact free-J power identity with an explicit port bound

`FreeJPowerFinish.graph_power` proves in an arbitrary model of `IΣ₁`, under
the actual 95-row free-J internal-zero, positive-coordinate and port
hypotheses β > 0, MC < β, MF < 2β, and the **additional model hypothesis
β ≥ 46**, that

```
X = 2ᴿ,    X = v₅,    q = 1 + v₀β,
R = ((q−1)(q−v₁)+v₂)(q²−1)+(MC+q MF)v₀.
```

Here `2ᴿ` is the model's internal exponential. The proof adapts the existing
2011 power-recovery argument to the actual twelve-variable graph: it combines
the exact first-carrier quotient, main-root orientation and exact main
index with the independently audited bound 2ᴿ < Y. It identifies separately
extracted main indices using Pell-coordinate injectivity. The first-carrier
scale is `(v₅v₆)v₆`, distinct from the auxiliary norm's Δ(f²−1).

The β ≥ 46 hypothesis is not discharged for the chosen compact44 port here.
This result does not remove the factor three from `q ∣ 3·2ᴿ`, interpret the
Mersenne port, calibrate the compact44 checker, prove existence of an iPRA
proof, or establish the final consistency equivalence. It is a conditional
model-level result in classical Lean metatheory.

## Evidence

The first exploratory session 11319 exited 1 due to two unresolved names;
its [source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained and its `sorryAx` is not proof evidence. Corrected session
10160 exited 0 with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) pins the independently audited growth parent,
matched seeds and inherited chains, compiles this suffix over fresh author
and peer overlays and verifies direct imports. It does not rebuild inherited
chains. The graph parent's manifest-at-read qualification and Foundation
outer-wrapper and package-transitive/dynamic ancestry limitations remain;
resource sampling is not a continuous whole-process-tree hard quota.

Outer session 44213 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `79b2ed9b277ec8647c217bcf90ca63d60eeaf3998cb5846ca5fb7b910e2c6af9`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-power-finish-new
```
