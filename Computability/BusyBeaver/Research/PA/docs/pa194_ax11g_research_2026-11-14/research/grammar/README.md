# Terminal grammar searches around AX11G

These are completed, unsuccessful searches for a 193-control machine in a
specified neighborhood of AX11G. They do not establish a lower bound.

| Search | Initial endings | Seed | Iterations | Accepted | Hits | Best score |
|---|---:|---:|---:|---:|---:|---:|
| Four terminal macros | 4 | 202611142233 | 4,638,201 | 248,305 | 0 | 60 |
| Admitted existing subtrees | 11 | 202611142288 | 5,197,642 | 283,588 | 0 | 60 |

Each run was allotted 300 seconds. The effective score is the number of
interned AX readers minus folds, with a separate structural penalty added for
ranking. The fixed part has 134 controls; effective score 59 with zero penalty
was the hit threshold. A score of 60 corresponds to 194 controls. The starting
AX11G construction attains that value with 67 readers and seven verified folds.
A hypothetical search hit would still need full source, folding, startup, and
logical validation.

## Search scope

`search.cpp` mutates binary grammar association, replacing a selected shared
subtree by a left or right rotation throughout the grammar. It interns shared
pairs and prices local context folds through `screen.cpp`. Near the frontier it
checks simultaneous compatibility of the chosen disjoint folds. Structural
penalties use the frozen `leaf_attrs.txt`; these guide the search and are not
proof certificates. The parameter-permutation branches in this particular
source are disabled (`if(false)`). Neither run exhausts all associations.

The four-endings input replaces the last `node49` by `node49`, `node55`,
`node58`, or `node70`. The broader input uses eleven existing subtrees admitted
by the symbolic stack screen in `price_safe_terminal.py` and priced at most 194.
The screen preserves a saved arbitrary initial formula `g`, checks additional
saved entries using its propositional/equality/universal validity rules, and
allows the resulting visible top to vary. “Admitted” describes this finite
screen; it is not an independent correctness theorem for every trial ending.

`price_padding.py` considered 49 endings (existing subtrees plus balanced repeats
of selected terminal macros) admitted by its narrower padding effect test. Its
minimum optimistic state count was 194, attained by three seeds.
`price_safe_terminal.py` admitted 14 existing-subtree endings; eleven had
optimistic count 194 and three had 195. These prices subtract a maximum disjoint
opportunity matching from the raw count; that price alone does not prove
simultaneous fold feasibility. Both complete price receipts are included.

## Files and provenance

The C++ sources, two template files, leaf attributes, both complete logs, header-only
hit CSVs, four initial trees, and all 60 final seed grammars are frozen inputs and
outputs from the recorded runs. The preparation and pricing wrappers now import
`../../construction/vendor/` and use `../../machine/`, without a checkout or
network access. Their finite outputs were replayed and compared byte for byte to
the frozen originals; see `summary.json` and `verification.json`.

`PROVENANCE.json` identifies the pinned ProveIt revision and compiler origin.
The underlying compiler provenance and licenses are in `../../construction/`.
These scripts and the two new runs were produced for this investigation.

## Replay

Run from the extracted package root with Python 3 and assertions enabled:

```sh
python3 -B research/grammar/verify.py
```

This inexpensive verification regenerates both price tables, the three padding
seed grammars, both C++ template inputs, and all four initial tree files. It also
checks the source/input hashes and recorded run summaries. It does not repeat a
stochastic search. Individual preparation commands accept `--output DIRECTORY`;
`prepare_safe.py` additionally accepts `--prices FILE`.

To repeat the timed experiments on a C++17 toolchain:

```sh
c++ -O3 -std=c++17 research/grammar/search.cpp -o /tmp/ax11g-terminal-search
/tmp/ax11g-terminal-search research/grammar/templates.txt research/grammar/leaf_attrs.txt /tmp/ax11g-run 300 202611142233 > /tmp/ax11g-run.log
/tmp/ax11g-terminal-search research/grammar/safe_templates.txt research/grammar/leaf_attrs.txt /tmp/ax11g-safe 300 202611142288 > /tmp/ax11g-safe.log
```

Wall-clock stopping makes the number of iterations and final pool dependent on
machine speed and scheduling. The frozen logs record the completed runs; exact
iteration counts are not promised by a rerun using the same time allowance.
