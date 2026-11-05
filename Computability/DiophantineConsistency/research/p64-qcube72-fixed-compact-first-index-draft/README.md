# First Pell index below fixed compact main rank

`FreeMainFixedCompactFirstIndex.first_index_lt_rank` proves that for any
IΣ₁ model, any natural K, and any actual positive zero of the 72 graph at the
fixed compact44 beta and masks, there is a model element `n` with `n<R` and
the first Pell coordinate identities

```
xcoord n (2(P−1)+1)=v₉,     2*ycoord n (2(P−1)+1)=k,
P=X Y²,  X=v₈q,  Y=q³v₇,  k=v₁₀+v₁₁.
```

Here `R` is the actual graph rank. The proof composes the checked first-norm
extraction, generic first/main comparison, and fixed compact main-rank
result. It assumes no old early congruence. This does not establish
`2n=R+1`, the old carrier, a reverse witness map, equivalence of the
72-operation equation, or an iPRA endpoint.

Attempt02 passed with Lean exit 0, the expected axiom report
`[propext, Classical.choice, Quot.sound]`, no warning or `sorryAx`, and stable
direct input guards. The source's historical unchecked-draft header predates
this check. The three guarded direct providers are the fixed compact
ranked-main, actual first-index extraction, and generic comparison objects.
Their transitive and dynamic ancestry is inherited, and resource usage is
sampled; this is not a source-only rebuild.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainFixedCompactFirstIndex.lean` | `8531fb5512662c7a13a11b840599179bf9f2a1bd5920dfb1d6cbc41ed447e113` |
| `check02.py` | `de6c3d94cd5b9e80d5311397acc7289e147c93b198442e14ee9097550fbe090e` |
| `observations/attempt02/compile.log` | `1ca00bbcdb188bad64f0168425469c3c3d2c447a6cb1340a90e9ebba1c481f35` |
| `observations/attempt02/result.json` | `a7e800847d346e5bfb9462973f4012e428de85ff205fed0c19bd26f6f380930d` |
| `/tmp/p64-qcube72-fixed-compact-first-index-priority-check02/FreeMainFixedCompactFirstIndex.olean` | `4537bb7943f48bf600027fc7d0c4fab35476a10fa25f8e94d381b5cdecaff20d` |

The run used a 2,400 MiB Lean limit, 120-second timeout, sampled 3.5 GiB
process-group RSS limit, minimum 10 GiB available memory, and low CPU/I/O
priority. Attempt01 failed before elaboration because the search path omitted
a transitive symbolic-port object. Its exact source, runner, log and receipt
are retained in `observations/attempt01/`; attempt02 added the missing path
without changing source.
