# Predecessor-specific state elimination on 21 K215 implementations

## Result and exact scope

No 214-state candidate was constructed by this work. The new executable search
allows **different incoming transitions to a deleted control to use different
existing continuation states**. It does not require one uniform surviving
control. This is a complementary finite grammar to the pair-fold searches in
the pinned repository; no claim of historical priority is made.

Inputs are the 21 literal native tables listed in `results/all_r5/summary.json`,
all from ProveIt commit `53269bcab1efc0f82d3022645bd7cf0c22d84959` under
`Computability/BusyBeaver/Research/ZFC/candidate-k215/`. The audit confirms
21 distinct rooted labelled transition graphs, also distinct after a global
reflection, and graph reachability of all 215 working controls in every input.
Graph reachability does not establish blank-tape reachability. These checks do
not upgrade any alternative's existing correctness status.

| Search | Actual result |
| --- | --- |
| All 21 tables, radius 5, 96-step bounds, same-row reentry allowed | 7,324,620 action trials; 8,475,730 local case tests; no deletion |
| Primary K215, radius 7, 192-step bounds | 970,351 abstract contexts; 348,300 action trials; no deletion |
| Coordinated primary state-40 repair, radius 5 / 96 | 731,000 provider trials; 1,812 surviving providers; 1,558,320 root action trials; no hit |
| Independent positive control | A live state is deleted using providers 8 and 9; 64 contexts independently replayed |
| Independent state-40 obstruction replay | Three abstract windows exclude all 860 root actions in the stated local-join grammar |

The finite window is an overapproximation: starting control is the table's
declared start, every initial local bit pattern is admitted, and either bit
may enter on every window shift. Consequently it contains every real run from
that control, including blank input, but can include unreachable contexts.
Its closure is the ordinary least fixed point computed by the inherited
finite-window worklist. No proof-assistant theorem is claimed for these search
programs.

The rejected action trials fall into these stopping categories:

| First failed case category | Trials over the 21 tables |
| --- | ---: |
| Candidate path leaves the known window before joining | 6,337,648 |
| Candidate halts without an admitted join | 56,397 |
| Candidate crosses another edited incoming row | 156,932 |
| Candidate exhausts its step bound | 16,448 |
| No old join configuration is obtained before the old-path restrictions | 755,940 |

These are failures of bounded sufficient certificates, **not semantic
counterexamples**. In particular an outside-window failure does not say that a
larger-window proof, a relational simulation, or a different table is wrong.
The zero-hit result is not a lower bound for Busy Beaver machines.

## The transformation and its sufficient theorem

Let `T` be an old deterministic machine, `q` a noninitial control, and `E` the
set of all external incoming rows whose old target is `q`. Form `U` by deleting
`q` and replacing each row in `E` independently; each replacement has any write
bit, either move, and any retained target or the original halt. Other rows stay
fixed. This gives 860 possible actions per row in a 215-state table.

At each old invariant context at an edited row, the search requires a positive
old path and a positive new path ending in exactly the same retained control,
head location, and tape. Both paths must read only cells represented in the
window. A path may use its own edited row repeatedly, because that row's proposed
action is already fixed. It may not cross another edited row before the common
configuration: those other actions have not been synthesized yet. The old path
may traverse the deleted control, but it cannot finish a macro there.

**Sufficient local-join theorem.** Suppose the invariant covers the old starts
and is inductive, every edited incoming row has such finite positive joins for
every old invariant context, and no new transition targets `q`. Then `T` and `U`
have the same halting behavior from those starts.

**Proof.** Synchronize both runs at equal configurations outside `q`. If the
current row is unchanged, take one identical step. Such a row cannot enter `q`,
because every external incoming row was edited. At an edited row, apply its
local join. The shared endpoint is a configuration reached by the old run, so
its invariant is available for the next synchronization. Equal finite-window
tapes and the fact that neither path reads outside the window imply equality
of the whole tapes for every exterior, since no exterior cell was modified.
Both macro durations are finite and strictly positive. Hence an infinite
sequence of synchronizations gives an infinite run in each machine, whereas a
finite run ending at the halt has a matching halt in the other machine.
Determinism identifies these constructed runs with the actual runs. This is an
ordinary mathematical sufficient theorem, not a compiled endpoint proof.

## The state-40 near miss

On primary K215 the three external incoming rows of 40 are `27/1`, `54/0`, and
`198/0`. The first can be rerouted to `0 L 302`; the third can use `1 L 54` or
`1 L 66`. No root action for `54/0` passed the search. The independent Python
replayer reduces this failure to the following three local windows. Bits are
listed from head-5 to head+5; the head is index 5, counted from zero.

| Mask | Window | Actions remaining after this and earlier windows |
| ---: | --- | --- |
| 80 | `00001010000` | `0 L 54`, `0 L 66`, `0 L 198` |
| 84 | `00101010000` | `0 L 54`, `0 L 66` |
| 320 | `00000010100` | None |

The receipt retains literal old control/head traces. These windows belong to
the abstract invariant and are not asserted to occur on the actual blank run.
The replay independently checks all 860 choices against just these three
windows using dictionary tapes, rather than the C++ bit-mask implementation.

The additional provider experiment fixes one of the two accepted `198/0`
routes and the `27/1` route, then changes one extra row. That provider's action
must first preserve its own old invariant contexts without relying on the
unsynthesized `54/0` row. Each surviving provider is combined with all 860 root
actions. All four edited entry contexts are rechecked against the joint table.
This is still a restricted grammar: arbitrary mutually dependent multirow
rewrites are outside it.

All 21 inputs share these four rows:

| Control | Read 0 | Read 1 |
| --- | --- | --- |
| 40 | `0 L 4` | `1 L 54` |
| 54 | `0 L 40` | `1 L 54` |

They implement a read-only leftward scanner for the first adjacent `00`.
Control 40 remembers a just-read zero; 54 remembers no pending zero. The two
histories are distinguished by the next symbol zero: 40 exits to 4, whereas 54
must continue. Thus an isolated read-only monotone scanner with the same fixed
exit and no external history needs two nonterminal controls. This elementary
finite-automaton fact explains the local obstruction. It is **not** a lower
bound on a machine allowed to write temporary marks, move both ways, share
other controls, change its data representation, or use a weaker simulation.

## A concrete next contract to change

The best next target suggested by this result is the combined register-file
excursion and return macro, rather than a further exact-tape replacement of
40/54. The current local symbolic specification in
`k225-formal/rocq/rocq-extension/coq/215/Runtime230Core.v` fixes the increment
box to `sepsR (incr r vs ++ [1])`. Its validity condition only needs at least
ten register-file entries and a possible branch condition on one of the first
nine. At the higher simulation layer, `Sim230.v` already hides the spare
extension existentially.

This suggests weakening **local synthesis contracts** to:

`input enc(p, registers, gap, spares) ->+ output enc(p', registers', gap', spares')`,

where the nine logical registers and the source continuation are exact,
`spares'` is any nonempty finite list of natural values, and `gap'` meets the
representation bound. The spare suffix need not equal the old suffix followed
by a fixed value. The existing zero-spare candidates change the appended value
to zero; this proposed search admits changes to old spare values and their
count as well.

The generic composition proof is immediate from the existential representation
relation, provided **every** primitive, the halt interface, and the exact blank
prefix are proved for the new relation with positive progress. The difficult
new obligation is a universally valid binary block contract for an actual
smaller table. No row may be changed merely because a spare value is logically
irrelevant: the new block must leave a valid nonempty physical suffix and
decoder uses of shared controls must continue to work. No machine satisfying
this relaxed contract has been constructed here. This is a concrete proposed
synthesis objective and a way to escape the exact whole-tape join family, not
a completed state reduction or a new equiconsistency theorem.

## Reproduction

Python 3 and a C++17 compiler suffice. No network or third-party Python package
is used. From this packet's root:

```sh
c++ -O3 -std=c++17 contextual_eliminate.cpp -o contextual_eliminate
c++ -O3 -std=c++17 repair40.cpp -o repair40
python3 check_controls.py
python3 run_search.py --source inputs --out /tmp/k215-elimination-r5 --radius 5 --cap 96 --reentry
python3 run_search.py --source inputs --out /tmp/k215-elimination-r7 --radius 7 --cap 192 --reentry --names primary
python3 audit_tables.py --source inputs --summary results/all_r5/summary.json --out /tmp/k215-table-classes.json
python3 prepare_input.py inputs/k215.native.tm /tmp/k215-primary.input
./repair40 /tmp/k215-primary.input 96 > /tmp/k215-repair40.json
python3 check_state40_obstruction.py inputs/k215.native.tm --out /tmp/k215-state40-obstruction.json
```

The 21 exact native input files, every per-table action list, aggregate receipts,
the independent control and three-window receipts, and graph classification are
included. Timing is incidental. This packet does not recompile the upstream
Lean/Rocq endpoint or rerun the full symbolic runtime of each alternative.
