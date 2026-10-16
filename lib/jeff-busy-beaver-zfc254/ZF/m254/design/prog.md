# zfc_254: program layer (L2)

Target, proved with no axioms (`Print Assumptions` reports "Closed under the global context"):

```coq
Theorem prog254 : rm_halts p254 ([], R0) <-> enum254_halts.        (* coq/Main254.v *)
Corollary prog254_iter : iter_halts p254 R0 <-> enum254_halts.
```

* `p254`, `R0` and `p254_wf` are the TM layer's frozen definitions in `M254.Prog254`
  (`../tm/coq/Prog254.v`). p254 is the decoder tree the Turing machine runs, built from
  `../inputs/paths.json`.
* `rm_halts` is `M254.RM`'s path semantics (zf/v335/coq/RM.v verbatim).
* `R0 = upd regs0 0 2`: nextproof = 2, every other register 0.
* `enum254_halts` is the frozen enumerator in `../logic/coq/Enum254.v`, started from s0 = all zeros.

This composes directly with the TM layer's `tm254_rm : halts tm c0 <-> rm_halts p254 ([], R0)`.

Build (Idle priority, one coqc at a time): `cd coq && python build.py Main254.v`. It takes about 2-5
min from clean, depending on load. `../logic/coq` and `../tm/coq` (RM, RMEquiv, Prog254) must already
be compiled with their owners' `build.py`. Full check: `python -I check.py`.

## Strategy

**L2 is proved on the 219-node Wade DAG, then bridged to p254 by a checked path-level bisimulation.**

p254 is not the Wade unfolding with its leaves permuted. The third party rebalanced the decoder tree:

* max depth is 34, against 96 for the unfolding of the Wade DAG;
* only 1 of the 6,460 (path, op) leaves coincides (`tools/cmp_tree.py`);
* so break/continue levels differ throughout.

A structured-semantics proof directly on p254 would therefore need its own lemma for each of about
1,000 irregular inlined loop instances. On the DAG, the method of zf/v335 (ProgLib/Prog) carries over
almost unchanged:

* about 50 shared atom lemmas;
* one symbolic run of `axioms()`;
* `Opaque P`, so no code value is ever computed.

## Files (`coq/`, logical root `M254P`; `M254L` = `../logic/coq`, `M254` = `../tm/coq`)

| file | content |
|---|---|
| Dag254.v | generated (`tools/gen_coq.py`): `dag254`, the TMBuilder compile of `source_local.py` (219 nodes, root 0 = main().0, registers in declaration order) |
| Bisim.v | generic: halting equivalence of two RM.v programs from a checked certificate (below) |
| Cert254.v | generated certificate: 3,010 related pairs of test-site IPs |
| Bisim254.v | `p254_dag : forall R, rm_halts p254 ([], R) <-> rm_halts dag254 ([], R)` (vm_compute, both directions) |
| ProgLib254.v | structured-semantics library on dag254: `St`, `sem`, node rules, 20 generated while-loops, pair, unpair, if_eq, if_not_decnz, the stack subroutines |
| L2Root254.v | `root_sem`: one run of the root = one `enum_step`; `iter_halts_dag` |
| Main254.v | `dag254_wf`, s0 → s2 in two steps, `prog254`, `prog254_iter` |

## The bisimulation (Bisim.v)

The only nodes that read a register are decnz leaves. Between two of them, a program runs only inc,
break and continue leaves.

* `seg t f P` runs such a segment on the IP alone. It returns the list of incremented registers and
  the IP at the next decnz or halt leaf.
* A certificate entry `(P1, P2, j, k)` relates two test IPs. They must be both halt leaves, or both
  `decnz r` with the same `r`.
* For each outcome of the test (nonzero goes to entry `j`, zero to entry `k`), the two segments must
  increment every register equally often and end at the IPs of the successor entry.
* Entry 0 is the pair of segments from the empty IP.

`check_sound` says that a passing certificate gives `rm_halts p1 ([], R) -> rm_halts p2 ([], R)`.
The proof is a strong induction on the exact halting step count of p1. On p1's side, `seg_hn` follows
the given halting run. On p2's side, `seg_run` builds the run. Registers are compared pointwise.
`mirror` gives the other direction.

For speed, the checker never calls `nodes` while walking. Each program is converted once into an
inductive tree (`to_tree`), and `walk_tree` proves that `walk = twalk`. So any computable
representation of p254 works. The Python generator `tools/rmpath.py` is an exact mirror of RM.v's
path arithmetic. It is not trusted: Coq re-checks every entry.

## The structured proof (ProgLib254.v, L2Root254.v)

This follows zf/v335/coq/ProgLib.v.

* Register files are related pointwise to a 9-field record.
* Straight-line nodes are flattened by computation (`expand`) into atoms.
* Atoms with control flow are proved by induction:
  * the loops through `sem_while`, with closed forms checked field by field;
  * `pair162`, the source's loop for `out += P(in1, in2)`;
  * `unpair115`/`116`, with `unP_step` iterations;
  * `if123_eq`/`_neq`, the destructive equality test;
  * `ifnot133`.
* The stack subroutines are run symbolically on clean registers:
  * pushwff, v_1, par1/2/3, cons = wim, wel, wal, weq, wn, wex, wa, read, pop.
* `ax1` runs all of `axioms()` symbolically. The resulting stack is syntactically
  `Enum254.ax_stack`. The current formula equals `gate` after a case split on the two destructive
  equality tests.
* `root_sem` composes the prefix (fetch the command, read the selector and param1) with the four
  dispatch branches.

The boundary invariant is scratch1 = scratch2 = axiomcode = 0 (`enc`).

## Interface notes

* Registers: nextproof 0, topwff 1, wffstack 2, axiomcode 3, param1 4, param2 5, scratch1 6,
  scratch2 7, prooflist 8 (source.py declaration order). This is the same numbering as the TM layer.
* The certificate depends only on the tree shape (fixed by paths.json), not on p254's node
  numbering; it is checked against the TM layer's frozen p254.
* `prog254_iter` uses the TM layer's `p254_wf`.

## Tools (`tools/`; run with `python -I`)

| file | purpose |
|---|---|
| `rmpath.py` | RM.v path semantics on trees, the p254 tree from paths.json, the DAG unfolding, the certificate generator |
| `gen_coq.py` | writes Dag254.v, Cert254.v |
| `gen_prog.py` | writes the generated regions of ProgLib254.v (loops, atom list) from Dag254.v |
| `cmp_tree.py`, `dump_dag.py` | diagnostics |
