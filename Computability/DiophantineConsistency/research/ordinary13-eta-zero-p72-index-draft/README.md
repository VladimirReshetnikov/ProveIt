# Model-natural eta: exact-index source draft

This is an **unelaborated, source-only draft**, generated from the repository's
`Lean/DiophantineConsistency/Compact44/P72Exact.lean` (pinned SHA-256
`a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3`).
The original file and its proofs remain unchanged. The generated copy imports
that original module and places its adapted declarations in a separate
namespace. `large_of_six` and `index_close` are copied unchanged; the two
requested theorem bodies derive from the original declarations, with the
changes described below. Attribution is to the authors of the pinned upstream
source; see that file and repository history for original provenance.

The intended theorem signatures preserve every original hypothesis and
conclusion except `(hη : 0 < η)`, which is removed. `η` is still a model
natural `V`, so its automatic nonnegativity is used and `η=0` is permitted.
The generated file retains the original first-Pell indexing and congruence,
main-Pell index and norm, strong norm, and auxiliary offset hypotheses. It does
not derive any of them from an equation.

In `index_window`, `c>0` is now proved after `k>0`, using `Y>0`, `k>0`, and
`η≥0`. The strict comparison `k<c` uses `Y≥2` and `k>0`; `2R<c` retains the
strict first inequality `2R<2(R+1)` and only requires `Y*k≤c`. In
`indices_ordinary`, the adapted call omits `hη` and `2≤c` uses `Y*k≤c`.
These are noncircular source-level proof adaptations; their Lean types and
all transitive dependencies remain **unchecked**.

Reproduce the source and result checks from this directory with

```
python3 -I -S -B generate.py > /tmp/eta-zero-p72-draft.json
cmp result.json /tmp/eta-zero-p72-draft.json
```

The default command checks bytes without changing the draft; `--write`
regenerates it. The generator first checks the exact upstream hash and
requires every individual replacement to match once. Its receipt certifies the
reproducible text transformation, not Lean compilation, theorem soundness,
provider compatibility, parity, graph-zero extraction, zero maps, or iPRA
endpoint. The file uses `.lean.src` to prevent it being mistaken for a built
module. No equation change or operation reduction is claimed.
