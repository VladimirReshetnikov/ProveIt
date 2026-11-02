# Free-J power projection

`FreeJPowerProjection.graph_projection` proves in every model of `IΣ₁`,
under the actual 95-row free-J internal-zero, positive-coordinate and port
hypotheses β > 0, MC < β, MF < 2β, that

```
q ∣ 3X  and  q ≤ 3X,    q = 1 + v₀β,  X = v₅.
```

It adapts the 2011 power-projection argument to the twelve-variable graph:
the actual first factor supplies `q³ ∣ Y`, the audited first-carrier result
supplies `k=R+1+4Qt` with `Q=(v₅v₆)v₆`, and the actual main-root orientation
provides the cancellation equation. This `Q` is the first-carrier scale,
not the auxiliary norm quantity Δ(f²−1).

This result **does not** identify X with 2ᴿ or remove the factor 3. The
Mersenne-port interpretation and exceptional-factor cancellation remain
separate steps, as do compact44 checker calibration, an object-level iPRA
proof, and the final consistency equivalence. The theorem is a conditional
model-level result using classical Lean metatheory.

## Evidence

The first exploratory session 43053 exited 1 on two local rewrites; its
[source](observations/attempt01.lean) and [log](observations/attempt01.log)
are retained, and its `sorryAx` is not proof evidence. Corrected session
95355 exited 0 with [no warnings or sorryAx](observations/attempt02.log).
The [paired replay](replay.py) pins the independently audited quotient parent,
matched seeds and inherited chains, compiles this suffix over fresh author
and peer overlays and verifies direct imports. It does not rebuild the
inherited chains. The graph parent's manifest-at-read qualification and the
Foundation outer-wrapper and package-transitive/dynamic ancestry limitations
remain; resource sampling is not a continuous whole-process-tree hard quota.

Outer session 6760 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `046ea7ed43ed4bce073bfd3a07cf59b2345aed4d9384361758887b9432cda10b`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-power-projection-new
```
