# Runtime and compiler interface investigation

This package records the runtime branch of the October 18, 2026 search below
245 states. It does **not** contain a verified machine below 245 states.

The main reusable positive result is an ordinary mathematical proof that
existing increment entries 39, 72, and 93 work on both incoming pointer bits,
with unchanged transitions and no state charge. This relaxes fine tokens
`A`, `T`, and `F`. The same proof applies to 70, 169, and 201. The mathematical
argument uses the inherited mark and increment induction contracts; its
literal premises have an executable checker.

The broader orientation survey found eleven further formerly one-sided
closed entries that passed every tested short outer prefix. Together with
the three increments, these give the fourteen-mask grammar search lane.
Only the three increments have the separate general orientation proof here.
The remaining survey results quantify register values and header slack, but
have finite control-prefix scope. Concrete compiled candidates must replay
their own actual paths.

A later fully unlocked fourteen-mask 128-rule grammar passed source
bisimulation but failed its actual machine replay. On blank it reaches a
right-ray writing trap after 51 steps. The main grammar package records this
counterexample. It illustrates the compositional boundary: atom interiors
after reassociation and the initializer also require proof. The fourteen-mask
survey must not be read as certifying that candidate.

The simultaneous two-entry deletion search covers a specified family of
51,439,104 action pairs and found no candidate accepted by all bounded exact
frame fixtures. This is a finite search result, not a lower bound on states.

## Files

- `runtime_results.tex`: report section for inclusion in the main paper.
- `increment_orientation_lemma.tex`: general six-entry increment argument.
- `check_increment_orientation_rows.py`: exact literal row-premise checker.
- `increment-orientation-row-check.json`: recorded successful premise check.
- `atom_orientation.py`: synthetic transparent decoder and unchanged affine executor interface.
- `atom-orientation-results.jsonl`: three-prefix survey including full-program state 150.
- `atom-orientation-short-results.jsonl`: complete legal outer prefixes of lengths 1 through 7, excluding 150.
- `classify_atomic_suffixes.py`, `atomic-suffix-results.json`: all 506 legal prefixes of lengths 1 through 8 for six remaining restricted entries.
- `coupled_two_entry.cpp`, `coupled-complete.jsonl`: completed simultaneous two-entry deletion family.
- `candidate245-literal-cases.txt.gz`: exact inherited finite fixtures.
- `joint-cost-candidate.json`, `joint-cost-run.json`: abstract joint grammar/scanner-cost lane, whose outcome and scope are recorded separately.
- `reference/`: unchanged minimal baseline dependencies, identified by `reference-manifest.json`.

The status strings are intentionally scoped. `PASS_LITERAL_PREMISES` checks
rows rather than induction proofs. `PASS_SYNTHETIC_CONTEXTS` checks the
declared concrete decoder contexts rather than all possible grammars. An
affine `FAIL` means the unchanged executor cannot justify that context under
its inherited contracts; it is not by itself a proof of nontermination or an
unbounded impossibility claim.

## Reproduce

Run from this directory using Python 3 and a C++17 compiler. The baseline root
is explicitly configurable through `ZFC245_BASELINE`.

```sh
export ZFC245_BASELINE="$PWD/reference"
python3 check_increment_orientation_rows.py
python3 atom_orientation.py
python3 atom_orientation.py --short
python3 classify_atomic_suffixes.py
```

The first full-program orientation survey is more expensive than the short
survey because state 150 contains 6,422 primitive leaves. Output JSONL files
are replaced deterministically apart from timings. The baseline affine
rules are copied unchanged in `reference/code/parametric_prefix_affine.py`.

To reproduce the completed deletion search:

```sh
python3 -c 'import gzip,pathlib; pathlib.Path("cases.txt").write_bytes(gzip.decompress(pathlib.Path("candidate245-literal-cases.txt.gz").read_bytes()))'
c++ -O3 -std=c++17 coupled_two_entry.cpp -o coupled_two_entry
./coupled_two_entry cases.txt rerun-coupled
```

All 54 eligible states are selected when no state arguments are supplied.
Individual states can be appended for a smaller reproduction. The complete
recorded run took about 1,213 seconds on the research worker; timing depends
on hardware and concurrent work. There are no positive deletion survivors.

The joint scanner/grammar-cost lane completed 6,826,542 iterations in
600 seconds. Its best cost remained 129: 128 grammar rules, maximum zero
run 6, maximum depth 43, and projected framework size 117. Thus it did not
reach the prospective 244-state threshold. Its final dictionary is an
abstract artifact and has no successful literal-table or blank-start proof.
The first coordinate of its property triple is the leading-zero bound.

```sh
c++ -O3 -std=c++17 joint-cost-inputs/anneal_fine_joint_cost.cpp -o anneal_fine_joint_cost
./anneal_fine_joint_cost joint-cost-inputs/grammar.txt joint-cost-inputs/constraints.txt rerun-joint.json 600 181804 128 joint-cost-inputs/lock0.txt joint-cost-inputs/resume.txt
```

The time bound makes iteration counts hardware-dependent. The input files,
source, random seed, final dictionary, and recorded counts are preserved.

## Baseline provenance

Dependencies are copied byte for byte from `zfc245-proof-20261018`, supplied
in ProveIt's `docs/incoming`. The machine is the Routing245 table, SHA-256
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.
The decompressed fixture SHA-256 is
`71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1`.
This package does not replace the full inherited proof package or its source
attribution. The report records no fresh proof-kernel endpoint.
