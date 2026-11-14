# Bounded compiler searches below 194 states

These searches did not produce a verified machine with fewer than 194 working
states. The successful `PA194C` construction elsewhere in this package is a
separate composition of the retained 194-state reader grammar with the cached
command controller. No stochastic search is required to reconstruct it.

`search_summary.json` is the authoritative receipt for the runs below. It is
generated from the retained logs by `summarize_searches.py`. A negative search
result concerns only the implemented proposals and fitness function; it is not
a lower bound on the size of a PA-consistency machine.

## Families and objectives

The first three families retain 134 fixed controls. The score before scanner
penalties is the number of distinct AX readers minus the number of compatible
two-cell contextual folds. An effective reader count of 59 would give a
prospective 193-state table, still requiring source and physical validation.

| Run | Changes proposed | Budget | Seed |
|---|---|---:|---:|
| `identity1` | Binary reassociation of the unchanged 190-token source word | 600 s | 111320263 |
| `joint1` | Reassociation and independent parameter permutations in six axiom heads | 480 s | 111320264 |
| `order1` | Reassociation and random permutations of six independent axiom heads | 300 s | 111320268 |
| `scanner1` | Reassociation with stricter scanner conditions described below | 400 s | 111320269 |

The first three completed respectively 9,385,957, 8,955,769, and 2,615,187
proposals. Each retained a best effective reader count of 60. That count
already occurs in the supplied starting grammar, so this is not a claim that
these runs constructed a new 194-state machine.

`order1` uses a dynamic program to reparse the permuted word while reusing
subtrees of its current grammar, followed by the same rotation proposals.
The six original half-open macro intervals are `[18,35)`, `[35,54)`,
`[54,70)`, `[70,86)`, `[86,102)`, and `[102,121)`. The run does not exhaust
all 720 orders or all grammars for an order. Parameter and head-order changes
would need an axiom-family and command-selector proof if a smaller candidate
were found; source equality cannot simply be assumed for these families.

### Shorter scanner experiment

The original return scanner uses fixed state 34. Deleting this state changes
the number of consecutive zeros that can safely occur in encoded source
addresses. `scanner1` therefore requires AX scanner attributes `m <= 5` and
`mi <= 4`, in place of the original `m <= 6` and `mi <= 5`. Its prospective
state target is 133 fixed controls plus 60 effective readers.

The run completed 6,895,063 proposals in 400.001 seconds. Its best penalized
score was 65: 67 raw readers, six folds, and penalty four.

This is only a necessary local search target. The outer controller and blank
initialization also need changes. The retained best grammar still has a
nonzero scanner penalty; it is not a valid smaller construction. The physical
scanner experiments and their concrete failures are recorded separately in
the structural research directory.

### Arithmetic representation experiment

The 190-token word has three runs of three increments of register T, beginning
at token indices 61, 73, and 89. The alternative `node61; dec T` computes
four increments followed by a decrement. Its numerical effect is
`(T + 4) - 1 = T + 3` for every natural T, and the decrement's zero branch is
unreachable at that point. `node61` and the decrement entry at native control
41 already occur in the fixed controller. The changed leaves may expose
different reader sharing and contextual folds.

`triple_inputs.txt` contains all eight choices of which runs to replace;
`triple_nontrivial.txt` omits the unchanged word. `triple1` mixed the unchanged
word with these alternatives and was stopped after its pool became dominated
by the old 194-state grammar. `triple2` searched only nontrivial alternatives
and did not improve its initial best of 63 effective readers. These two runs
were interrupted, so the receipt states the last recorded proposal count and
time, not an exact final count. No complete correctness certificate for a
new machine is claimed from this arithmetic experiment.

## Reproduction

The C++ searches need a C++17 compiler. From this directory:

```sh
g++ -O3 -std=c++17 search_identity.cpp -o search_identity
./search_identity start194.txt leaf_attrs.txt identity_replay 600 111320263

g++ -O3 -std=c++17 search_joint.cpp -o search_joint
./search_joint start194.txt leaf_attrs.txt joint_replay 480 111320264

g++ -O3 -std=c++17 search_reorder.cpp -o search_reorder
./search_reorder start194.txt leaf_attrs.txt order_replay 300 111320268

g++ -O3 -std=c++17 search_shortscanner.cpp -o search_shortscanner
./search_shortscanner start194.txt leaf_attrs.txt scanner_replay 400 111320269
```

The input files contain their own fixed table rows and grammar templates.
They need no network access or external checkout. The runs compact their
grammar caches every 5,000 proposals; the recorded Linux runs additionally
used a 100 MiB address-space limit. Proposal counts depend on computer speed
because the stopping criterion is elapsed time. The fixed seeds specify the
pseudorandom proposal stream, not a computer-independent final iteration.

`search_triple_only.cpp`, `triple_nontrivial.txt`, and `triple_attrs.txt`
reproduce the nontrivial arithmetic family. Its recorded seed is 111320267;
the planned budget was 480 seconds, but the actual run was stopped early.
`search_triple.cpp` and `triple_inputs.txt` describe the preliminary mixed
pool, with seed 111320266. `triple_variant.py` regenerates these inputs using
the bundled source compiler. `start194C.txt` is the six-row cached-controller
variant of the same numerical input; its zero-budget score check is a
diagnostic, not an additional optimization run.

`outer_rotations.py` enumerates single rotations of reachable named source
subtrees and compares the entire resolved 3,673-instruction graph. Its source
resolver was separately checked against the bundled compiler. A useful
remaining observation is that replacing

```text
node170 = (node36, node169), node36 = (node28, node35)
```

by

```text
node170 = (node28, (node35, node169))
```

changes just one resolved instruction: site 3660 jumps to site 34 instead
of site 25. Retagging the right leaf of `node166` from `continueTo 3` to
`continueTo 4` restores exact equality of all 3,673 resolved instructions.
It shortens the first Shift address from `100000` to `10000`.
`check_outer_rotation.py` directly repeats the equality check using the
bundled compiler; `outer_rotation_retag.json` records its observed result.
This is a source-level observation; the required physical route and complete
scanner deletion have not been established.

The optional Python source experiments use the frozen compiler at
`../../reference/pa194/construction/`. They do not require Lean or Rocq.

## Attribution and proof scope

`screen.cpp` and `search_plateau.cpp` are retained from the supplied PA194
packet; the latter was itself derived from the earlier PA195 research.
The other search drivers modify this inherited evaluator. The applicable
James Chang and ProveIt licenses remain under
`../../reference/pa194/construction/licenses/`.

The evaluator checks simultaneous local fold compatibility. Its fitness,
scanner attributes, and search logs are discovery evidence, not a substitute
for the complete source-map, register-interface, blank-start, and arithmetic
calibration proofs required for a consistency machine.
