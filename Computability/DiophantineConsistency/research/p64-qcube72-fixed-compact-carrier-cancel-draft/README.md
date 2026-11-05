# Same-zero compact index and free-carrier cancellation

`FreeMainFixedCompactCarrierCancel.fixed_data` proves, in any IΣ₁ model, for
an actual positive 72-graph zero at the fixed compact44 beta and masks and any
natural K, that one can choose model elements `n,s,e,mu` satisfying

```
n<R<2n, k=2n+4P*s, 0<e, Y²=e*mu, e|9,
0<mu, q⁴≤mu, mu|v₁₃,
```

along with both first Pell-coordinate identities for that same `n`. Here
`q=p₀v₀+1`, `Y=q³v₇`, `P=(v₈q)Y²`, `k=v₁₀+v₁₁`, and `R` is the
actual graph rank. The proof composes the same-index window/residue with the
generic cancellation, deriving the free carrier from this same zero. It
does not assume the old early congruence, prove the old carrier or index
equality, establish reverse existence, or supply an iPRA endpoint.

Attempt01 passed with Lean exit 0, stable direct guards, no warnings or
`sorryAx`, and expected `[propext, Classical.choice, Quot.sound]` axioms. The
source's unchecked-draft header predates this check. Direct guarded providers
are the checked same-index residue and generic carrier cancellation objects;
transitive/dynamic ancestry and sampled monitoring are inherited. This is not
a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainFixedCompactCarrierCancel.lean` | `902ab9d30f07dcc7cdcca28c6103862aecaf3ce5bed34c979576a8c133d0d70d` |
| `check01.py` | `7e11bfdbbb151a42701d683d260570e35b6c75391f4f10eb516a524dd7e38289` |
| `observations/attempt01/compile.log` | `e0ae0e4572ac6c5e8d24945dd2a587d287432731c8c548070f1eafb47446e5b0` |
| `observations/attempt01/result.json` | `e24fcbe237a4d47bb162855ab80b45eaddddae235614416ec39450efc8bc3d81` |
| `/tmp/p64-qcube72-fixed-compact-carrier-cancel-priority-check01/FreeMainFixedCompactCarrierCancel.olean` | `3dbbbc7253c3c0976f39adf9450d35e8b3280e098641c330268d7a9573b69434` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority.
