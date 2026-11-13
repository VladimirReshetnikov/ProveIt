# Generic main-index and carrier rigidity

`FreeMainScaleRigidity.same_rank_root_carrier` proves in every IΣ₁ model
that two Pell coordinates at the same parameter `a` and ordinate `c` have
the same indices and x-coordinates. If they also satisfy the displayed free
carrier identities with the same `X,Y,a,c`, their h coordinates are equal.
It uses strict monotonicity of the Pell ordinate and positivity of `4a+3`.
This generic theorem does not assume or extract actual graph zeros and does
not by itself prove a 72-to-76 obstruction or any existence result.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and expected `[propext, Classical.choice, Quot.sound]` axioms.
The source's unchecked-draft header predates the check. The direct guarded
provider is the captured `ArithmeticPellCongruences` object; transitive and
dynamic ancestry and sampled monitoring are inherited. This is not a
source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainScaleRigidity.lean` | `bfac36175e2e1b2374070520bc093e0d993ccf562a967d5616c3a80c7d0a5050` |
| `check01.py` | `72be6c4f1ef609156bbd87f1f5abfb5c6e938dffc3aadc81d1ffa96c31ede80c` |
| `observations/attempt01/compile.log` | `1a878e175fbcb99b9b16eb0b56e87d93d995eb9c96a4595e533d44ff1dfa434b` |
| `observations/attempt01/result.json` | `66c0b65df5b1232da05f2ed7e08d15259878fd66537e634f7d6334ad7ee770cb` |
| `/tmp/p64-qcube72-scale-rigidity-priority-check01/FreeMainScaleRigidity.olean` | `e941510c2b0d68559d80a4264c11ac3cf0c2714c00dd3335f9e754e9a2cf5fcc` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
