# Short-transfer experiments: rejected implementations and one open 215-state machine

**Status:** these files are research evidence, not an additional calibrated Busy Beaver bound. The `scratch-biased` experiment has a complete all-natural physical runtime certificate and an exact blank-tape bootstrap, but its changed scheduler has not been proved cofinal or safe above the arbitrary protected tail. The other three physical implementations are rejected.

The calibrated candidate elsewhere in the packet is the permuted **composite** transfer machine. Do not substitute a machine from this directory for it.

## Reproduction

Run with ordinary Python 3, assertions enabled:

```sh
PYTHONDONTWRITEBYTECODE=1 python reproduce.py
```

This reconstructs every source and all 430 transition rows from pinned parent data, checks the exact source transformations, reproduces the three failed primitive certificates, and replays the complete 69,744-transition scratch-biased blank bootstrap plus its matching 172-step abstract AX prefix. No optimizer or third-party dependency is required.

The universal physical proof for the open experiment can be rederived with:

```sh
PYTHONDONTWRITEBYTECODE=1 python reproduce.py --runtime scratch-biased --out /a/new/output/directory
```

Fresh optional runtime verification writes to a new output directory and compares every case summary against the fixed evidence; it does not rewrite the archived evidence.

The delivered `verification/scratch-biased-runtime.json` and compressed ordered case file record that run. It proves all 6,152 literal primitive cases over arbitrary natural primary-register values, arbitrary extra gap, every nonempty finite spare list, and the entire tape including the blank exterior. It covers all 430 transition rows, uses 1,617,669 symbolic rules, and has minimum literal duration 6. The symbolic proof-construction loop bound does not bound any represented register value or actual machine runtime. This is an executable mathematical checker, not a proof-assistant kernel artifact.

## What the shorter command does

Write the work tuple as `(t,w,d,h)`, and let `unpair(w)=(a,v)`. The proposed 35-leaf command first clears `t`, then copies `h` into `t` while restoring `h`, then invokes the inherited 26-leaf NIP. It therefore halts exactly when the incoming cache `h=1`; otherwise it returns `(h,v,d,a)`.

The arithmetic body is 35 leaves rather than the delivered parent's literal `DROP;NIP;NIP` body of 78 leaves. The latter additionally tests the incoming top: its exact halt condition is `h=1 OR t=1`. The short implementation was already priced at the source/raw-allocation level in the parent's independent compiler review, so the short command itself is not claimed as a newly invented calculus. The new work here diagnoses failed contextual allocations, repairs the physical implementation in a different way, and isolates the resulting scheduler proof obligations.

## Rejected physical implementations

| Experiment | Source DAG nodes | Leaves | States | Reason for rejection |
|---|---:|---:|---:|---|
| `simple` | 201 | 4,732 | 215 | The first new clear-top decrement reaches native122 in a context that selects cache register5 instead of top register1. |
| `simple-permuted` | 201 | 4,732 | 215 | The same concrete register-routing error after swapping the S/MP tags. |
| `context-root` | 201 | 4,732 | 215 | Clear-loop context is repaired, but the retagged return `CC3` at address `10011` uses an inherited physical entry that requires a different suffix. |

The first two allocations are a useful warning: an exact decoder-prefix check does not establish a primitive's meaning when its physical entry reads preceding code bits. Native122 has `122/0=0 L137`, after which native137 chooses between CD5 and CD1 using that preceding bit. The new occurrence violated the required context. A finite explicit counterexample for the permuted case is retained in `evidence/simple-permuted-counterexample.json` when available.

The context-root source was obtained by moving the clear loop across the selector boundary, changing the escaping `CB1` to `CB2`, rotating the outer Scheduler/Read composition, and finally replacing that return by `CC3`. These transformations preserve the complete ordinal register-program CFG. They do not by themselves preserve physical primitive-entry contexts. Its failed return is at source ordinal4,696, before the new clear loop at4,697.

The bounded single-row repair search tried all860 write/direction/target actions for native310/1 in the exact unpatched context-root table, with a350-rule symbolic proof-construction cap. It found no passing action. This is only a bounded-search result for that table and primitive; it is not an impossibility theorem. The exact table is pinned by the candidate recipe and the raw search receipt is in `evidence/cc3_entry_search.json`.

## The physically verified scratch-biased experiment

Replace the problematic `CC3` leaf by the already-shared pair `(CI6,CC3)`. The final return address now ends in `111`, satisfying the retained physical helper's context. This keeps the source at201 DAG nodes, with4,733 leaves and215 working states. The native table starts in state74 on an all-zero tape and uses the zero-spare refill row `198/0=0 L40`.

The pair is located at the **outer selector return**, so it executes after **both AX and MP**, not just MP. The command tags are `S=0`, `MP=1`, and `AX(c)=c+2`. The theorem-producing work-tuple operations remain the short S, inherited MP, and inherited AX; the newly nonzero scratch register changes subsequent enumeration.

At exactly69,744 transitions, the machine reaches native dispatcher84 with head at−2, header at62, and the exact source address

```
10010010010110110110
```

which is source ordinal64. The logical register vector `(N,T,W,A,D,H,X,Y,L)` is

```
(1,4,0,0,0,0,3,10,0).
```

There are65 spare blocks, with values0 or1. The entire finite set of one-cells is recorded. Abstract execution from AX entry25 and seed `(1,0,3,0,0,0,0,0,0)` reaches exactly this source state after172 primitive steps. Thus the physical startup is a genuine partial AX execution above an arbitrary tail3. This matches the same ten-head protected-stack interpretation used by the parent command compiler, but future scheduler safety still needs proof.

### Exact changed parser behavior

Let `X` be logical scratch register6, `L` the residual proof code, and `N` the next-candidate counter. At an ordinary command boundary, `X=0` after S and `X=1` after MP or AX. All other parser scratch registers are zero.

The inherited read loop with initial `X=b`, for `b` equal to0 or1, returns `unpair(n+b)` when its input residual is `n`. It again leaves `X=0` and the other scratch register zero. Consequently:

* At a positive residual, Schedule decrements first. The first command field is read from `unpair(L-1+b)`. The remaining command fields are read normally because that first read clears `X`.
* At an empty residual, Schedule copies the old next-candidate counter into `L`, clears `X`, and increases the counter by `1+b`. The newly started candidate is therefore decoded without bias, but the counter can skip a candidate number.

These equations can be verified directly against the source CFG. They do **not** imply that the old wire encoding, cofinal-success theorem, or old protected-credit estimate transfers.

### Remaining obligations

The physical implementation has passed. Logical calibration is **open**. A complete claim requires an explicit wire compiler compatible with the stateful first-field bias, a cofinality theorem for the actual candidate sequence despite counter steps of1 or2, and a protected-stack credit bound for that changed schedule. The retained universal strong command-block proof alone does not supply these three facts. No equivalence to `Con(ZFC)` is asserted for this experiment.

A more conventional return repair using `(CI4,CC3)` would instead raise MP/AX's retained offset before returning. That attempted source costs202 DAG nodes and216 physical states. Its strong compiler also does not transfer automatically: PUSH, DISCARD, and the offset-setting macro all require changes. It is not one of the four delivered215-state tables.
