# Equality alternatives on the exact K219 backend

The six requested clean equality alternatives produced no allocation with at
most218 states. The established allocators rejected all six because a required
right-child increment entry was absent. A separately labeled, unverified
CI6-right entry gave220 states under origin reuse for four alternatives. This
is a bounded allocation result, not a lower bound or a runtime certificate.

## Exact six-source batch

Each source replaces the same four literal accepted-hit10 occurrences. The
ordinary all-natural proofs are in [proof.md](proof.md) for0/1/2/3/12 and
[hit11-and-stacking.md](hit11-and-stacking.md) for11. Both complete source CFG
resolvers agree for every output. The five previously stored candidate sources
were regenerated exactly; hit11 was generated against the same K219 source.

| Hit | Source DAG / leaves | Established original and protected allocators | CI6 hypothesis: origin reuse | CI6 hypothesis: protected |
| --- | --- | --- | ---: | ---: |
| 0 | 207 / 4748 | Reject: no right CI5 entry | Not tried | Not tried |
| 1 | 207 / 4748 | Reject: no right CI6 entry | 220 | 242 |
| 2 | 207 / 4744 | Reject: no right CI6 entry | 220 | 240 |
| 3 | 207 / 4748 | Reject: no right CI6 entry | 220 | 242 |
| 12 | 207 / 4748 | Reject: no right CI5 entry | Not tried | Not tried |
| 11 | 206 / 4744 | Reject: no right CI6 entry | 220 | 239 |

The hypothetical successor adds exactly `CI6/right = 1 R 13`, as in the
separate decoder lane's earlier hit2 experiment. It is selected only after the
specific missing-right-CI6 rejection; the original failed result is retained.
All eight resulting tables pass exact decoder-prefix binding and retain302.
Every one of the four compiler versions reproduces the exact219 baseline table
as an identity control. There were12 established-policy attempts and8 explicit
hypothesis attempts. Hit2's previously measured outcome is reproduced here as
part of the uniform six-source batch; it is not a new discovery.

The [result](results/equality-allocations.json),
[raw stdout](results/equality-allocations.stdout.txt), and
[complete output archive](results/equality-allocations.tar.gz) preserve the
six sources, all20 individual outcomes, eight raw tables, identity controls,
and exact script. Runtime, startup and the hypothesized entry contract were
not tested. In particular, fewer source nodes did not reduce hit11's origin
allocation below220.

Reproduce using a fresh directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/measure_equality_allocations.py \
  --output /tmp/k219-equality-allocation-fresh
```

This script calls the pinned allocator functions in the sibling
[compiler snapshots](../k219-continuation-search/compiler-inputs/), after
reading their exact source and verifying their identities. It does not invoke
their command-line main functions, a binary runtime checker or a proof assistant.

## Comparator-only register exchange

The successor inventory uniformly substitutes each of the16 submitted hits,
both unchanged and with registers5 and6 exchanged, for all four comparators.
All32 whole-source CFG checks pass. No exchanged source improves on206 nodes:
exchanged hits10 and11 have207, and the other exchanged hits have207–209.

Register exchange is sound for every already-proved clean equality macro.
Conjugate each primitive transition by the permutation exchanging5 and6.
The exchanged macro on inputs(a,b) has exactly the original macro's execution
on(b,a), with the final register permutation reversed. Equality is symmetric;
both outputs are zero, and the other registers are fixed. Consequently the
exit, termination and complete register contract are unchanged for all natural
inputs. This reasoning transfers a contract; it does not establish contracts
for the remaining historically finite-tested hits.

The unchanged hits7/9 and exchanged hits4/5/8/14 use only already-available
generic leaf entries at their new internal nodes. These six are potential
next allocation experiments, but their ordinary all-natural contracts are not
proved in this packet. Every exchanged member of the seven proved families
still needs a CI5/CI6 or CD5 right entry. The generic-entry inventory does not
model origin reuse retaining a context-specific entry, so a listed missing
entry alone is not a compiler rejection.

The [inventory](results/equality-swaps.json),
[stdout](results/equality-swaps.stdout.txt), and
[all32 exact sources](results/equality-swaps.tar.gz) are retained. No candidate
allocator was invoked during this inventory. Reproduce with:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-source-search/inventory_equality_swaps.py \
  --output /tmp/k219-equality-swaps-fresh
```

Replacing5/6 by a different pair is not justified by symmetry alone: the
operands are stored in5/6, and the surrounding program must retain its other
registers. Such a transformation needs a separate operand-transfer and
restoration contract, including its source and binary costs.
