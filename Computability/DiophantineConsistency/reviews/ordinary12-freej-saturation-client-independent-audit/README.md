# Independent conditional free-J saturation audit

This reviews paired evidence `33f69b2663`. In every IΣ₁ model, the compiled
`FreeJSaturationClient.graph_saturation` proves two NoCarry conclusions for
model variables under **all** the following assumptions:

- a positive zero `v` of the exact free-J literal, `p₀>0`, `p₂<p₀`,
  `p₃<2p₀`, every `vⱼ>0`, and `p₀≥46`;
- `d≥3`, `N>0`, `q=1+v₀p₀=2^(dN)` and `v₀=rep(d,N)`;
- `p₃=HP+p₀`, `p₂<2^d`, `HP<2^d`, `p₂ mod 2=0`, `HP mod 8=4`,
  `population(p₂)+population(HP)=d`, and `HP·v₀≥1`.

The conclusions are `NoCarry(q−v₁−v₂−1, p₂v₀+1)` and
`NoCarry(v₁, HP·v₀−1)`. Port symbols are standard natural inputs interpreted
in the model. The theorem does not discharge the stated radix, split, mask,
residue and population hypotheses for the actual compact44 tuple; it does not
calibrate the checker, simulate a machine, or establish an iPRA derivation.

The independent audit verifies all ten frozen source/object/log and
same-side direct-import rows, the full 109-object inherited overlay on each
side, matched sibling outputs, pinned input hashes and the exact named axiom
report. It reruns both the independent conditional graph-population parent and
the source-closure audit. The outer wrapper session 46258, all ten compiler
steps and all ten dependency queries are recorded as exit 0. The terminal
record reports launch HEAD `8750eed704e41c19d002fd77868a8bb8977232a5` and
three loader variables removed before Python; this audit checks that record,
not a continuous external HEAD/environment history.

Each side's `ArithmeticBinaryCarry` log contains exactly the four permitted
linter warnings (two `unnecessarySimpa`, one `unusedTactic`, and one
`unreachableTactic`) with the prescribed full path/locations/text. No other
warnings, errors or `sorryAx` occur. The exact `graph_saturation` report lists
Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`. The earlier
single-side exploration and warning-policy review are not substituted for
this paired result.

Inherited Foundation outer-wrapper and package-transitive/dynamic ancestry
limits remain. RSS monitoring is sampled, not a hard process-tree quota;
`--deps` and audit subprocess timeouts are not whole-tree resource bounds.
Hashes are point-in-time checks, and original `/tmp` providers are needed.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-saturation-client-independent-audit/audit.py
```

Actual read-only audit session 13118 exited 0; no Lean compilation was
started. See `CHECK.json` and `terminal-observation.json`.
