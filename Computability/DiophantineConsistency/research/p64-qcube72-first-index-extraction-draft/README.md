# First Pell index from an actual 72-graph zero

`FreeMainFirstIndexExtraction.first_index` extracts and classifies the first
Pell norm of any actual positive 72-graph zero, with arbitrary natural ports,
in any IΣ₁ model. If `q=p₀v₀+1`, `Y=q³v₇`, `X=v₈q`, `P=XY²`, and
`k=v₁₀+v₁₁`, it produces a model element `n≤k` with first Pell coordinates
`xcoord n (2(P−1)+1)=v₉` and `2*ycoord n (2(P−1)+1)=k`. It uses the
checked first residual and positive-parameter classification. It assumes no
port bounds or old carrier congruence. This theorem alone does not compare
`n` with the main index or prove reverse existence.

Attempt01 passed with Lean exit 0, stable direct guards, and expected axiom
report `[propext, Classical.choice, Quot.sound]`, without warning or
`sorryAx`. The source header says “Unchecked draft”; the check applies to
those exact source bytes. Its two direct providers are the checked graph
residual and `ArithmeticPellFirstNorm`; transitive/dynamic ancestry and
sampled monitoring are inherited, and this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainFirstIndexExtraction.lean` | `58f91276267968ffe93169fbb225387a3e0b26bf7ddf1a1177c3744ce872c9ba` |
| `check01.py` | `ac4a74356124f1a9c3c859f62f55ecffc56510efe56ee9355fbf813df5ef45df` |
| `observations/attempt01/compile.log` | `17db198d332551177d2b7e70fdd5cc916608b4a2d64cc6eb231f178e0c55deff` |
| `observations/attempt01/result.json` | `3bfcae3d84fff56e41529b64a8330b0548e6a8073b7c1cc12ac06d13b9b4b622` |
| `/tmp/p64-qcube72-first-index-extraction-priority-check01/FreeMainFirstIndexExtraction.olean` | `67ed132545d507e96b24bf023cf91a51c6b5623902889bc36daaa55ad39ad785` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
