# Free-carrier cancellation in IΣ₁ models

`FreeMainCarrierCancel.cancel` proves the following in any IΣ₁ model. If
`q≥3`, `Y=q³y₀` with `y₀>0`, and

```
Y²*g = Y²*(X+(X*Y+Y)*c) + (4*(X*Y+Y)+3)*h,
```

then there are model elements `e,mu` with `e>0`, `Y²=e*mu`, `e|9`,
`mu>0`, `q⁴≤mu`, and `mu|h`. It applies checked gcd cancellation to the
free carrier and uses the `P64Early` common-divisor and size arguments. No
old early congruence is assumed. This generic theorem has not been composed
with an actual 72 zero or the same-index residue; it does not prove the old
carrier or reverse existence.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and expected axiom report `[propext, Classical.choice, Quot.sound]`.
The historical source header says “Unchecked draft” but this check applies to
those exact source bytes. The direct provider is the captured `P64Early`
object. Transitive/dynamic ancestry and sampled monitoring are inherited; this
is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainCarrierCancel.lean` | `f3ebf63fcf2ecf26936d8394ee74bc578937752223e4a6753da236d1784c99d0` |
| `check01.py` | `6fd3cf9dc29294c90b46bfc67e596ec526fb904a8f8fd87d78ff5f3f0ae717ab` |
| `observations/attempt01/compile.log` | `ae4e9a7b0e23b456811531eb93c2d18bf11be8989b0e7d0b4a8a16b3641f30df` |
| `observations/attempt01/result.json` | `50de53e9add381bc15c72821307b143984f1b191c1ce51ee347dda6b4ac3b9ef` |
| `/tmp/p64-qcube72-free-carrier-cancel-priority-check01/FreeMainCarrierCancel.olean` | `e43083918e775c396704e341db1268495c369a7d7b9b7f01fc207adb90775ef1` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
