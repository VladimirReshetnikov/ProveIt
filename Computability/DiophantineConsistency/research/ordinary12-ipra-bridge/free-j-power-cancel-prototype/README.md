# Conditional Mersenne cancellation for the free-J graph

`FreeJPowerCancel.graph_divides_power` proves in an arbitrary model of `IΣ₁`
that `q ∣ 2ᴿ`, assuming all of the following in that model:

* the actual 95-row free-J literal has an internal zero at twelve positive
  coordinates;
* the port bounds β > 0, MC < β and MF < 2β, and the additional β ≥ 46;
* a model element `d` with `d ≥ 4` and the **explicit port equation**
  `β = 2ᵈ − 1`.

Here `q = 1 + v₀β`, `2ᵈ` is the model's internal exponential, and
`R = ((q−1)(q−v₁)+v₂)(q²−1)+(MC+q MF)v₀`. The proof combines the audited
graph projection `q ∣ 3X`, the independently audited identity `X = 2ᴿ`,
and the existing Mersenne factor-three cancellation theorem. No assumption
that Δ divides the ordinary multiplier is introduced.

Neither β ≥ 46 nor β = 2ᵈ−1 has been discharged for the actual compact44
port here. The theorem does not calibrate that port's checker, prove
existence of a proof in iPRA, or establish the final consistency equivalence.
It is a conditional model-level result in classical Lean metatheory.

## Evidence

Exploratory author session 91245 [exited 0](observations/attempt01.txt), with
[no warnings or sorryAx](observations/attempt01.log). The [paired replay](replay.py)
pins the independently audited power-identity parent and matched seed
objects and inherited chains, then compiles this source over fresh author and
peer overlays and checks direct imports. It does not rebuild inherited
chains. The graph parent's manifest-at-read qualification and Foundation
outer-wrapper and package-transitive/dynamic ancestry limitations remain;
resource sampling is not a continuous whole-process-tree hard quota.

Outer session 18464 [exited 0](evidence/terminal.txt), printing receipt
SHA-256 `e352772228bbaa752ee58f698acab67b26c596231390e05944db210683c73c26`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0 and matching objects; [author](evidence/author.log) and
[peer](evidence/peer.log) reports have only `propext`, `Classical.choice` and
`Quot.sound`, with no warnings or `sorryAx`. Independent review of this new
suffix remains required. When the pinned temporary parents remain available
and the Lean slot is free, reproduce with:

```
python3 -I -S replay.py --output /tmp/ipra-freej-power-cancel-new
```
