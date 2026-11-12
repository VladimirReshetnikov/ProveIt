# Eta-natural prototype: conditional model proof that X>0

This is an **unelaborated source draft**, not a checked theorem or an iPRA
endpoint. It uses the exact generated eta-natural prototype and the proposed
prototype factor-unit bridge, plus the separate prototype `J_positive` and
residue-graph-independent `Residue90XZeroArithmetic.xzero_impossible` fact.
It assumes ports are casts of natural `p : Fin 4 → ℕ`, and explicitly assumes
`0 < (p 0 : V)` for the model-cast beta. The first-factor J proof also uses
natural `K0=p 1≥0`. A fixed compact-port beta proof is separate.

The prototype graph has `X=q*(v 6)` and `Y=q³*(v 7+1)`. The prior prototype
J draft and positive beta give `q≥2`; the shifted s input `v 7+1` gives
`Y≥q³`. If `v 6=0`, then `X=0`, `a=Y`, and its own signed main root has

```
z = U*(Y*c) + H*t,
U=Y*q², H=3+4Y,
z²=U²*(1+(H+Y²)*c²),
```

with t the *actual signed prototype shift*. In particular, it has no
`X*Y*q` term and the signed rank need not be model-natural. The reused
fact-level argument uses signed square divisibility and signed-to-natural
divisibility reflection to derive `H∣U`, hence `H∣3q²`, contradicting
`3q²<H` from `q≥2` and `Y≥q³`. No positivity of eta, zeta, c, gamma or the
signed rank is assumed by that arithmetic lemma. In the actual graph
`eta=v 9`, `zeta=v 10+1`, and `k=eta+zeta`; in particular the source is
intended to cover eta=0 and the shifted zeta remains positive.

The proposed `witness_positive` concludes `v 6>0`; `X_positive` then concludes
`q*v 6>0` using the exact graph input relation. Neither proves a nonzero
value for an unrelated graph. Graph factor extraction, model port casts,
source/provenance and tactic elaboration, fixed compact beta, actual eta-zero
contradiction, zero maps and the internal endpoint remain open. `#print
axioms` appears only as unexecuted source.

Run `python3 -I -S -B research/ordinary13-eta-natural-X-positive-model-draft/check.py`
from `Computability/DiophantineConsistency` and compare with `receipt.json`.
The check pins sources and performs finite exact graph/algebra controls; it
does not execute Lean or prove arbitrary-model statements.
