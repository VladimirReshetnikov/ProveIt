# Free-J power growth with an explicit port bound

`FreeJPowerGrowth.X_lower` and `FreeJPowerGrowth.growth` prove in an
arbitrary model of `IΣ₁`, under the actual 95-row free-J internal-zero,
positive-coordinate, and port hypotheses β > 0, MC < β, MF < 2β, and the
**additional model hypothesis β ≥ 46**, that

```
X ≥ 16  and  2ᴿ < Y,    X = v₅,  Y = v₆,
q = 1 + v₀β,
R = ((q−1)(q−v₁)+v₂)(q²−1)+(MC+q MF)v₀.
```

`2ᴿ` denotes the model's internal exponential function. The first result
uses the independently audited `q ≤ 3X` projection; the second combines
X ≥ 16 with the exact first and main Pell indices and the existing
`power_bound` theorem. The first-carrier scale used there is
`Q = (v₅v₆)v₆`, distinct from the auxiliary norm's Δ(f²−1).

The separate β ≥ 46 hypothesis has not been discharged for the chosen
compact44 port here. The theorem does not yet identify X with 2ᴿ, remove the
factor three, calibrate the compact44 checker, produce a proof in iPRA, or
establish the final consistency equivalence. It is a conditional model-level
result in classical Lean metatheory.

## Evidence

The first exploratory session 62455 exited 1 on an index-expression rewrite;
its [source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained and its growth `sorryAx` is not proof evidence. Corrected
session 9877 exited 0 with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) pins the independently audited projection
parent, matched seeds and inherited chains, compiles this suffix over fresh
author and peer overlays and verifies direct imports. It does not rebuild the
inherited chains. The graph parent's manifest-at-read qualification and the
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain; resource sampling is not a continuous whole-process-tree hard quota.

Outer session 78120 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `e87b5ae91986a25cbdaa50feb764be74a1b934047bda4d9ff8669bd44d72392a`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-power-growth-new
```
