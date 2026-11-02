# Independent preliminary saturation closure review

This reviews source scan and draft `e2ffe09c90`. It is a **point-in-time
source-only plan**, not a simultaneous source freeze, a paired Lean build, a
proof of graph premises, complete package/dynamic ancestry, or an iPRA proof.
The reviewed client was an uncompiled draft at this commit; any later
single-side exploration requires its own evidence and does not constitute a
paired replay.

The author scan reruns byte-identically (exit 0) and its optimized invocation
fails closed (exit 1). The independent check validates the source hash, unique
source path, parsed direct-import list, reachable dependency order and leaf
availability for both sides. Exactly four missing modules are reachable:
`ArithmeticBinaryCarry`, `ArithmeticSaturation`, `ArithmeticRepunit`, and
`ArithmeticMaskPopulation`. Both inherited graph-population overlays contain
109 matching recorded object paths; their current hashes and resolved paths
match the pinned scan. The independent graph-population parent receipt is
pinned and its completed status is checked; this source-only audit does not
rerun that long parent artifact audit.

The draft's two NoCarry conclusions are conditional on the positive free-J
literal zero and port inequalities, `p₀≥46`, `d≥3`, `N>0`,
`q=1+v₀p₀=2^(dN)`, `v₀=rep(d,N)`, a split `p₃=HP+p₀`, digit bounds
`p₂,HP<2^d`, residues `p₂ mod 2=0` and `HP mod 8=4`, the population
identity `population(p₂)+population(HP)=d`, and `HP·v₀≥1`. These are
hypotheses, not conclusions of the closure scan. A later coherent build must
freeze its sources, validate every same-side direct dependency, retain the
inherited parent limitations, and verify actual paired exits and axiom reports.
No compact44 port calibration, checker, machine simulation or PRA bridge is
established here.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-saturation-closure-independent-audit/audit.py
```

Actual audit session 74040 exited 0 and did not run Lean. It reads original
`/tmp` providers and current source bytes; absent or changed files fail
closed. Hash checks are point-in-time observations, not a continuous or
simultaneous snapshot.
