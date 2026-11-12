# Compact eta-natural rank lower bound and conditional early index

These source-only drafts are **not Lean-elaborated**. They target the exact
eta-natural prototype, inherit its unelaborated graph and factor-unit sources,
and do not prove eta-zero impossibility or an iPRA endpoint.

For the model-natural rank

```
R=((q−1)*(q−F)+alpha)*(q²−1)+(MC+q*MF)*J,
```

all subtractions are truncated in the model naturals. Since the graph shifts
`alpha=v2+1`, the first coefficient is at least 1 even without a positive-C
assumption. If `q≥6`, then `q²−1≥26`, so `R≥26`. The bound applies to this
natural rank even when `q<F`; identification with the **signed graph rank**
requires `F≤q` and the separate gap/rank representation theorem.

`compact_rank_at_least_26` proposes to obtain the stronger `q≥47` from the
prototype's own J-positive source and the separate compact first-port bound.
K is arbitrary natural; the fixed kernel/file/PDF representation, imports
and providers remain independent obligations.

`compact_early_index_of_norms` composes the proposed prototype J and X
positivity, `R≥26`, the compact rank window and the eta-natural early-index
source. It keeps the natural first root tau and **both actual first/main norm
premises explicit**, including the no-`E*q` natural signed-pair shape. Its
conclusion preserves the same first root tau, index n and quotient w; it does
not construct the strong/auxiliary witness, main Pell index or the eta-zero
contradiction. The main norm's identification with the graph requires the
positive-C rank representation and prototype-specific signed-factor/natural
magnitude conversion; no original residue graph zero is implicitly imported.
The later parity client still requires its exact strong and absdiff auxiliary
premises, `R≥26`, the eta=0 equality and coherent same-witness bindings.

Run `python3 -I -S -B research/ordinary13-eta-natural-rank-index-model-draft/check.py`
from `Computability/DiophantineConsistency` and compare with `receipt.json`.
The check pins sources and performs finite natural controls, not Lean, provider
or model proof checking.
