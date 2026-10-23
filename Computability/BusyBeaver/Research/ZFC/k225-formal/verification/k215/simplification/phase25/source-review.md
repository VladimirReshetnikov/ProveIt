# Source review and boundaries

All declarations and imports retain their previous public types. The source-only
reviews preceded compilation; their earlier pending labels remain historical.

| Module | Proof simplification | Lines removed | Bytes removed |
|---|---|---:|---:|
| `FirstOrder.Calculus` | Context membership, renaming normalization and semantic environments | 71 | 1,275 |
| `ConstructibleAbs` | Existing `isFunctionOn_iff` transports the first three approximation fields | 7 | 457 |
| `KRuntimeCore` | Shared split and constructor elimination in left/right peeling | 10 | 104 |
| `KSim` | Optional-execution witnesses and residual-time arithmetic | 9 | 362 |
| `KZip` | Existing list normalization at recursive scan endpoints | 4 | 124 |

The constructive context proofs use `List.forall_mem_cons`; the existing
`List.map_subset` replaces image-witness bookkeeping. The two failed elaboration
sites were repaired by applying the implicit membership argument explicitly and
unfolding `up` on a successor. These repairs change no proof obligation.

`KSim.checkEdge` and the entire `sim_step` body remain byte-identical. Thus this
proof-only change does not alter the existing literal certificate acceptance
computation. The full dependency-transitive rebuild remains required for changed
proof objects. All fifteen typed compatibility clients retain their source bytes;
six depend on changed proofs and must compile fresh.

Only accepted phase24 supplies reusable objects. The focused diagnostic result is
used to inspect elaboration and compare seven declaration profiles; it is not a
full endpoint basis. Its failed first attempt, prior unexecuted calculus drafts,
raw compiler output and later corrections remain distinct.

The separate paired-decrement experiment intentionally changes `checkEdge`.
Its two execution budgets need not accept exactly the previous certificates.
Any future adoption must freshly check all 45 variant batches and integration;
a three-block comparison cannot establish that acceptance or a general speedup.

The normal upstream comparison found no new changes beyond the previously
attributed Claude integration. This batch authors proof changes in this worktree.

The direct calculus probes find a strict improvement: `cons_sub` originally used
`propext` and the final proof is axiom-free. All six other ordered profiles match.
The first comparison deliberately required equality and therefore records a FAIL;
its compiler results and discrepancy are preserved. A separate readback checks
exactly this one specified reduction without another compiler invocation or a
change to the full 93/5/10 profile gates.
