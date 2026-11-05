# Fixed compact 76Y zeros have q not divisible by 3

`FreeMain76FixedQNotThree.fixed_q_not_divisible` proves in every IΣ₁ model:
for arbitrary natural K, any actual positive zero of the 76-operation
independent-y graph at the fixed compact44 beta and masks satisfies `3∤q`,
where `q=p₀v₀+1`. This is a theorem about the checked 76Y graph; it does
not assert the existence of a positive 72 or 76Y zero.

The proof reconstructs the checked forward map's specific witness update
`u=update v 13 h`, where the checked positive main-gap theorem supplies h.
It shows u is a positive 72 zero, retains the same q,Y,k,R, and converts the
difference-ring gap identity into the exact same-coordinate old-carrier
identity. The checked conditional 72 no-gamma theorem then contradicts
`3|q`. Thus the conclusion does not rely on choosing an unrelated 72 witness.
It does not by itself settle the reverse existential implication.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and the expected `[propext, Classical.choice, Quot.sound]` axiom
report. The source's unchecked-draft header predates this check. Direct
providers are the checked 76-to-72 forward package and the conditional
no-gamma object. Transitive/dynamic ancestry and sampled resource monitoring
are inherited, so this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMain76FixedQNotThree.lean` | `2366738263d44e4f47151cdd0bddcdc6df5248f03f21f90b225d03494e647e0a` |
| `check02.py` | `37cafa316bf6435e0a2b68d9835f3c26c3cc3c264a65ee10e839c2a753bd0728` |
| `observations/attempt02/compile.log` | `5e0c88edfc7200e96c356a63359189dcbe887b449f2d7ce8dded6e6fae56de50` |
| `observations/attempt02/result.json` | `ce9ebcac40c25f2b00141720997462aac6c2821f8ec930253b4875f77eaf1d3b` |
| `/tmp/p64-qcube76y-fixed-q-not-three-priority-check02/FreeMain76FixedQNotThree.olean` | `4c96d138cf57ad19a37add34eacbc2a4f2f6d156baad90e235a530b07d3b7ef6` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed on a cast-normalization goal and produced no
object; its report contained `sorryAx`. Its exact source, runner, log and
receipt are retained under `observations/attempt01/`.
