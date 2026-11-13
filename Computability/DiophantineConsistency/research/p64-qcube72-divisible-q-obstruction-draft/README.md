# A 3-divisible q obstructs divisibility of the free-carrier witness

`FreeMainDivisibleQObstruction.not_dvd` proves in any IΣ₁ model that, for
model elements `q,w,s,U,g,c,h`, if `3|q`, `U>0`, and

```
X=wq, Y=q³s, a=XY+Y, H=4a+3,
g² = 1+(a+1)(a+3)c²,
U*g = U*(X+a*c)+H*h,
```

then `U` does not divide `h`. The result permits any positive `U`; it does
not require `U=Y²` or graph-specific assumptions. The proof assumes `U|h`,
cancels the positive `U` in the carrier, and shows `3|g`, while the main
norm gives `g²≡1 (mod 3)` because `3|a`. This generic theorem alone does
not establish that any graph zero has `3|q`, or any global failure of a
reverse implication.

Attempt02 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and the expected `[propext, Classical.choice, Quot.sound]` axiom
report. The source's unchecked-draft header predates the check. The single
direct provider is the captured `ArithmeticPellRecurrence` object;
transitive/dynamic ancestry and sampled resource monitoring are inherited,
so this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainDivisibleQObstruction.lean` | `7e19722acface5914c82b8fb2ff2c7339e4dfd6f62ce06060aa75fc8d0358aad` |
| `check02.py` | `d3811cd65713592949eef5e9075adb2b69a6e1677d29d3b98fe92a4afcb998a3` |
| `observations/attempt02/compile.log` | `4ea8de6fee328c05237e2077e587bab6e42678fb0e25ca643176677f96e61df4` |
| `observations/attempt02/result.json` | `2bdaf6a476857e0679a055e8c88558fcc6a1a13366a56de30758af0464c80e22` |
| `/tmp/p64-qcube72-divisible-q-obstruction-priority-check02/FreeMainDivisibleQObstruction.olean` | `f8ed9da0c9bbce5cbd049cd928f6c342b13f04ef90275b8e6668741d7932f30b` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed on a local rewrite order and an unavailable
additive-divisibility lemma; its source, runner, log and receipt are retained
in `observations/attempt01/`, and its error report contains `sorryAx`.
