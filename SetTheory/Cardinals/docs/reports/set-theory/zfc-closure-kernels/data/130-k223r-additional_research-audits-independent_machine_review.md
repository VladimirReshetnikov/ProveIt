# Independent audit of the K223 machine and three folds

## Result

The delivered table contains exactly **223 working states and 446 transitions** over the binary alphabet. The halt target is separate: canonical states are `0,...,222`, start is `0`, and halt is `223`. Every declared working state is reachable in the directed transition graph. This graph statement does not assert that every state is visited on the blank computation.

The independent checker in `independent_machine_audit.py` passed. Its receipt is `independent_machine_audit.json`. It imports only Python's standard library and reads the supplied construction as data; it does not import the construction's fold checker, builder, compiler, or runtime engine.

The canonical table SHA-256 is:

```
0d4eb8ffbcd5dc025c8dac198c7d8a15404c35f63134b5e3ed0b7df7673d9231
```

The K-label table SHA-256 is:

```
5bcee335bc5cf45b6ebc6d1f97a10e3cc8aae2af303b82c5cc9ce506a4d22ed7
```

## Independent fold proof

The checker reconstructs the three transformations from `portable/folds/folds.json` and checks that their composition equals the literal final table. For each stage, it independently enumerates every assignment to the finite set of tape cells relevant to each invariant implication. This proves initiation and consecution for all literal transitions. These truth tables cover arbitrary infinite extensions of each finite pattern; they are not samples of reachable computations.

Next it checks every supplied exceptional block against the new literal table. Every read must concern a cell fixed by the old invariant or the current read symbol. Every write is recorded, and the entire finite patch, head position, and mapped control state must equal the old one-step endpoint. All cells outside that patch remain unread and unwritten. The checker requires a positive number of transitions in every block.

| Stage | Fold in K labels | Inductive fact in the old table | Positive blocks |
| --- | --- | --- | --- |
| 226 to 225 | `191 → 157` | At 157 the preceding cell is 0; at 191 it is 1 | 3 steps for either old-157 branch, 5 for either old-191 branch |
| 225 to 224 | `303 → 118` | At 159 the following cell is 0; at 118 the current cell is 0 | 1 step for each of the three possible old branches |
| 224 to 223 | `302 → 159` | No tape fact required | 1 step for all four branches |

For the first fold, the new shared rows are `157/0 → 0 L 67` and `157/1 → 1 L 187`. They read the incoming predecessor tag and return through existing code. The only cells touched by the exceptional blocks are offsets -1 and 0. Their original contents are restored before the endpoint at head offset +1.

For the second fold, the fact at 159 follows from the literal predecessor `(152,0) → (0,L,159)`. Its right-hand zero is the bit just written. The transition `(159,1) → (1,R,118)` then gives the current zero at 118. The old branch `118/1` is impossible. Replacing it by `1 R 153` lets 118 absorb 303. The checker proves this invariant on the **225-state table before that fold**. It does not incorrectly apply the fact to the merged state afterward, when read 1 becomes possible.

After the second fold, states 302 and 159 have identical rows, so the third fold is an ordinary quotient. All nonexceptional rows at every stage agree exactly under the corresponding state map.

These facts imply the following theorem by induction on the old computation:

> For every binary tape on the integers and every initial head position, the 226-state parent and the 223-state result, each started in state 0, halt together.

The initial invariant at state 0 is empty. Thus this fold theorem does not assume a blank tape or a register-machine frame. A finite old computation concatenates finitely many finite blocks. An infinite old computation concatenates infinitely many positive blocks, none containing an earlier halt. Consequently the theorem is an equivalence of halting behavior, not merely a one-way finite-prefix simulation.

Three negative controls were independently rejected: a false predecessor tag, omission of the supporting fact at 159, and an incorrect replacement for the reclaimed read-1 branch.

## Literal table and bootstrap binding

The audit checked both relabeling maps as bijections and checked every mapped transition. The runtime legacy table, K-label table, and canonical table therefore denote the same machine. The canonical numbering was independently reconstructed by breadth-first graph traversal, visiting read 0 before read 1.

The builder simulates initialization in K labels. This audit instead simulated the **canonical** table from the all-zero tape for 409,835 transitions. It reached canonical dispatcher 22 at head -5 and matched the complete stored support of the tape, not only selected registers:

| Property | Independently checked result |
| --- | --- |
| Logical primary registers | `(3,0,0,0,3,0,0,0,0)` |
| Logical-to-physical register positions | `(6,2,0,4,3,7,8,5,1)` |
| Header distance from head | 181 |
| Spare registers | 167, each of value 1 |
| Tape cells containing 1 | 351 |
| All other cells | 0 |

The compact JSON serialization of the sorted set of all one-cell positions, followed by a newline, has SHA-256 `2f1158059a8021e206c790eeb43509d0b2c4bb3b73471ab47edcb73242e61772`.

## Universal runtime review

The K223 files `runtime/symbolic_runtime.py` and `runtime/independent_runtime.py` are **byte-for-byte identical** to their counterparts inside the vendored K224 archive. Their respective SHA-256 values are:

```
c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145
0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346
```

The reviewer inspected the generic engine and K223 adapter. The engine's accelerated operations have ordinary induction justifications:

1. A literal transition is used directly.
2. A same-state scan across a unary run is justified for every natural run length by induction. A run that may be empty can be skipped only by that rule; an ordinary literal read requires a provably positive length.
3. An arbitrary finite list of spare blocks is traversed only after deriving its one-block schema afresh from the actual table, with opaque left and right contexts. The general traversal follows by list induction. The four required entry schemas are rederived for each table.
4. Whole-tape normalization uses exact word identities, including `C(A)1 = 1B(A)` for the same finite list A, where `B(v)=0 1^(v+1)` and `C(v)=1 0 1^v`, and the corresponding reversed identity.

The runtime adapter pins the exact legacy table and source; derives all four block schemas; and checks all 5,956 instruction/guard cases. Frames quantify over nine independent natural register values, an arbitrary natural extra gap, an arbitrary first spare value, and an arbitrary finite remaining spare list. Nonhalting instruction cases must return the exact whole tape, source successor, and head displacement. Halting cases must reach the literal halt target. Every case has a strictly positive affine duration. The 4,000 symbolic-step cap only limits proof search; an unfinished derivation is rejected.

The independent audit checks the stored runtime receipt's bindings, exact guard coverage, positive durations, 1,431,799 symbolic steps, and coverage of all 446 literal transition rows. It does **not** substitute receipt inspection for a fresh universal replay. The main construction replay is the separate operation that reexecutes the engine on all cases; that replay was run by the primary reviewer and reported successful.

## Scope and reproduction

This audit proves the three-fold machine equivalence, validates the literal table representations, and exactly checks blank initialization. It also reviews the unchanged universal runtime proof rules and checks their file binding. Logical calibration of the new source to ZFC consistency is covered by separate source/calculus artifacts. The certificate is executable ordinary mathematics that can be formalized in ZFC; it is not a new Lean or Rocq kernel endpoint.

From the construction root, with this file and its checker placed in `additional_research/audits/`, run:

```sh
python additional_research/audits/independent_machine_audit.py \
  --portable portable \
  --output additional_research/audits/independent_machine_audit.json
```

The checker performs no writes except its explicitly named output receipt.
