# Three source controls in the final AX gate

This component investigates source indices **4560**, **4572**, and **4578** in
the parent K215 register program. It supplies a bounded trace, an independently
replayed short entry prefix, an exact literal-address classification, and an
ordinary mathematical argument using inherited totality theorems. It does not
supply a new proof-assistant reachability theorem, a simulation of a modified
machine from blank tape, or a 214-state consistency calibration.

## Bounded execution

The supplied initial checkpoint configuration is vertex 25 with the nine
logical registers `[4,0,0,0,0,0,0,0,0]`. The separate machine experiment reports
this as the first decoded parent frame after 79,633 binary-TM transitions.
That machine-to-source frame identification is an input to this component.
All transition counts below are **source-checkpoint transitions**; they are
neither binary-TM transitions nor individual register instructions.

`reachability_probe.py` pins the checked graph's SHA-256 and performs exact
integer arithmetic. It accelerates a positive self-loop only when the tested
register is not replenished. If its current value is `q`, this expands to
exactly `q+1` checkpoint transitions. Every other test executes once.

| Bound on accelerated edges | Expanded checkpoint transitions | Target visits | Final vertex | Maximum register bits |
|---|---:|---|---:|---:|
| 100,000 | 26,416,175 | None of the three | 695 | 24 |
| 1,000,000 | 27,765,638 | None of the three | 695 | 24 |

The 100,000-edge final registers are
`[7,0,8713544,0,0,0,109,163,0]`. The one-million-edge final registers are
`[7,0,8263901,0,0,0,643,343,0]`. Both runs visit 238 distinct checkpoint
vertices. The second trace spends most of its time inside a long arithmetic
loop. The absence of a target in either finite prefix is not an unreachability
proof. The ordinary argument below establishes eventual visitation without
computing the enormous intermediate formula codes or their execution time.

`crosscheck_direct.py` independently executes ordinary checkpoint transitions,
without importing the accelerated interpreter and without drain acceleration.
It matches all eleven recorded boundaries through 31,323 ordinary transitions
(the first 10,000 accelerated edges). It also records every configuration of
the initial prefix through the first AX entry.

## Exact AX entry and routine classification

The direct interpreter reaches **vertex 26 after exactly 180 checkpoint
transitions**, with registers `[7,0,0,0,0,0,0,0,0]`.
The checked leaf mapping and literal `DagPerm.v` identify vertex 26 as the
first primitive in `dagPerm`'s AX routine, node 236. In the inherited `AS`
encoding the register order is

`np, tw, ws, ac, p1, p2, s1, s2, pl`.

The initial AX state therefore has `np=7` and every other field zero. In
particular it satisfies `Clean`, which requires `s1=s2=0`.

All three target instructions occur in the mandatory final gate of that AX
routine, at node 457:

| Source index | Literal source address | Location within the reference gate | Meaning |
|---:|---|---|---|
| 4560 | `110100100111010110000` | First `ifeq_clear`, initial `CD5` | Compare `c` with `B` |
| 4572 | `11010010011101100` | `loop211`, initial `CD7` | Restore saved `c` from scratch 7 to scratch 6 |
| 4578 | `110100100111100000` | Second `ifeq_clear`, initial `CD5` | Compare `c` with `A` |

The literal gate nodes are
`457=(192,458)`, `458=(131,459)`, `459=(211,460)`, and
`460=(197,131)`. Node 192 duplicates `ac` into the scratch registers and
clears `ac`; node 131 compares scratch 6 against parameter 2, clears both,
and clears `tw` on equality; node 211 transfers scratch 7 to scratch 6;
node 197 transfers parameter 1 to parameter 2. Both comparisons terminate
normally, regardless of equality, and both are always called.

`check_semantic_binding.py` checks the pinned literal data independently of
the graph generator. It follows the reference source paths through the
literal DAG, checks the opcodes, checks the common AX/gate occurrence, and
checks the six concrete checkpoint rows needed for the gate calculation.
The semantic roles use the inherited theorem sources, whose exact pinned
identities are in `inherited_provenance.json`.

## Ordinary eventual-visitation argument

The inherited module
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2AxiomsPerm.lean`
provides the following ingredients:

- `AXAtom.run` proves a finite normal run for each AX macro on a `Clean`
  state.
- `axWord_checked` binds the macro word to the literal AX nodes and its final
  gate node 457.
- `axWordRun` composes these normal runs and the final gate.
- `l457` sequences `loop192`, the first `ifeq_clear`, `loop211`, `loop197`,
  and the second `ifeq_clear`.
- `l236` gives the complete finite normal AX run.

The macro contracts `loop192`, `ifeq_clear`, `loop211`, and `loop197` are in
`L2Perm.lean`; the state encoding is in `L2Lib222.lean`, and `Clean` is defined
in `L2Macros222.lean`. These are inherited theorem sources. The separate final
Lean integration receipt reports whether their dependency modules were
recompiled in this packet. The Python scripts in this directory do not
re-prove those theorems and do not invoke the Lean kernel.

From the all-zero AX fields, `AXAtom.effect` shows that every macro before
the gate preserves `ac=p1=p2=s1=s2=pl=0`: all formula/stack operations change
only `tw` and `ws`; the two field-read operations read zero from `pl=0`.
Consequently the finite normal macro sequence reaches checkpoint 4556, the
first primitive of the gate, with

`[7,T,W,0,0,0,0,0,0]`

for finite natural numbers `T,W`. Their values need not be evaluated.
The concrete checkpoint graph then forces these steps:

1. Vertex 4556 tests zero register 3 and enters 4560 after one transition.
2. Vertex 4560 tests zero register 5 and enters 4564. Vertex 4564 tests zero
   register 6 and enters 4570. Thus 4570 is reached after three transitions
   from the gate entry.
3. Vertex 4570 drains register 1 from `T` to zero and exits to 4572. This
   drain takes exactly `T+1` transitions, so **4572 is reached at offset
   `T+4`** from gate entry.
4. Vertex 4572 tests zero register 7 and enters 4575. Vertex 4575 tests zero
   register 4 and enters 4578. Thus **4578 is reached at offset `T+6`**.

The target offsets from gate entry are therefore **1**, **`T+4`**, and
**`T+6`**. The expression `T+1` is the length of the clear loop, not the
offset of the first target. All three target instructions test a zero register
on this particular first AX execution.

The finite 180-step prefix, exact literal binding, and inherited total normal
macro runs give an ordinary mathematical argument that the **parent source**
eventually visits all three addresses from the supplied initial source state.
The source graph is deterministic, and its branch/segment binding to the
literal programs is checked in the separate affine-core component. No
assumption of ZFC consistency is needed for the finite AX macro execution.

This rules out dismissing the three addresses as unreachable in that parent
source run. It does **not** establish that any mutated physical machine
follows the parent until these controls, reaches the same valid frames, or has
a different blank-tape halting behavior. A wrong uniform primitive contract
and a missing consistency calibration remain different statements. We have
not added a kernel theorem composing the entry prefix, intermediate trace
events, and source/binary simulation.

## Portable reproduction

The intended archive location is `state_search/source_reachability/`, alongside
the common `affine_core/` component. From this directory:

```sh
python3 reachability_probe.py --graph ../../affine_core/input_graph.json \
  --out /tmp/k215-reachability-100k.json

python3 crosscheck_direct.py --graph ../../affine_core/input_graph.json \
  --receipt reachability_probe.json --out /tmp/k215-direct-replay.json

python3 check_semantic_binding.py --graph ../../affine_core/input_graph.json \
  --leaves ../../affine_core/leaves.json \
  --dag ../../affine_core/source_deps/K215F/DagPerm.v \
  --out /tmp/k215-semantic-binding.json
```

The optional larger trace uses `--edges 1000000`. Both interpreters are bounded
and use exact Python integers. The accelerated probe also limits register bit
lengths to 4,096. Reproduction writes new receipts; elapsed times naturally
vary. The original accelerated script is retained byte for byte so that its
two recorded source hashes remain valid.
