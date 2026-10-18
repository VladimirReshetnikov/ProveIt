# Reproduction notes for the state-reduction lane

The final routing search produces the concrete 245-state machine packaged in
`reference/candidate245/`. Its separate macro, affine, register-bisimulation
and logical audits are supplied elsewhere in the archive. This lane supplies
independent grammar, literal-fixture and blank-bootstrap checks, plus the
reproducible search. Earlier near-misses remain explicitly identified below;
most abstract grammars alone do not establish a machine theorem.

The register witness is a precise obstruction to direct exact-value aliasing.
The pair-merge sweeps are finite evidence on stated fixture families.

The archive manifest assigns this lane's files to `code/state_reduction/`,
`inputs/state_reduction/`, `results/state_reduction/`, `reference/`, and
`report/`. Commands below run from the archive root. Generated executables
and decompressed fixtures are temporary and need not be committed.

## Exact register witness

```sh
python3 -B code/state_reduction/safe_lifetime_witness.py \
  --program reference/source/Prog254.v \
  --dag reference/source/Dag254.v \
  --output results/state_reduction/safe-lifetime-witness.json
```

The two independent source interpreters must agree after 13517 source
instructions. Both the original theorem-safe witness and the all-positive
variant appear in the result. This does not assert reachability from the
particular blank bootstrap and does not rule out packed or reconstructed
register representations.

## Finite pair-merge sweep with bootstrap resources

```sh
python3 -c 'import gzip,pathlib; pathlib.Path("resource-merge-cases.txt").write_bytes(gzip.decompress(pathlib.Path("inputs/state_reduction/resource-merge-cases.txt.gz").read_bytes()))'
g++ -O3 -std=c++17 code/state_reduction/resource_merge_search.cpp -o resource_merge_search
./resource_merge_search resource-merge-cases.txt
```

This writes `merge-search-summary.json` and `merge-survivors.txt` in the
current directory. The recorded result is 120540 candidates,76 past the
initial probes, and zero full survivors across 8385 fixtures. This is a finite
screen with 20000 moves per case and a bounded tape window, not an
inequivalence or minimality theorem.

Optional exact fixture regeneration:

```sh
python3 -B code/state_reduction/make_resource_merge_cases.py \
  --metadata reference/interval/instruction-metadata.json \
  --literal-helper reference/literal/check_literal_instructions.py \
  --table reference/tables/zfc_prefix246_old.tm \
  --output resource-merge-cases-regenerated.txt
```

The inherited metadata supply physical register representatives. The new
fixtures have header distance 181 and 167 spare blocks, all of value 1.

## Scanner bootstrap contraction

```sh
python3 -B code/state_reduction/check_short_scan_boot.py \
  --table reference/tables/zfc_prefix246_old.tm \
  --baseline-bootstrap reference/bootstrap/bootstrap.json \
  --output results/state_reduction/short-scan-boot.json
```

Both sparse and dense interpreters must reach the baseline endpoint after
407915 moves. The script checks the three-zero premise of all 1410 local
contractions. The unchanged source is already known to reject this shorter
scanner during ordinary execution; successful initialization is not a
runtime certificate.

## Independent routing-grammar checks

```sh
python3 -B code/state_reduction/check_route_grammar.py \
  results/state_reduction/gradient-repaired.json \
  --inputs reference/grammar \
  --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt \
  --output results/state_reduction/gradient-repaired-audit.json

python3 -B code/state_reduction/check_route_grammar.py \
  results/state_reduction/gradient-zero6-k129.json \
  --inputs reference/grammar \
  --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt \
  --output results/state_reduction/gradient-zero6-k129-audit.json
```

The first object is a rejected near-miss: it has 128 grammar rules and a single seven-zero AST node. It fails the universal affine audit at a zero-decrement case. A bounded literal replay does not establish a valid replacement contract; failure of that audit is not by itself a proof of eventual behavioral inequivalence.
The second has 129 rules and maximum zero run 6. Both preserve all 22 folded
projections and the 54 bootstrap locks. The fixed-state charge is 118 after
state 177 is replaced by routing through the grammar. Deleting scanner 74
would reduce that charge to 117. Thus the two objects are respectively
245-state and 246-state *proposals* after that additional scanner edit.
The first is rejected by that audit; the second passes as a 246-state intermediate machine.

The last risky source leaf of the 128-rule object is mapped reproducibly:

```sh
python3 -B code/state_reduction/map_reassociated_leaf.py \
  results/state_reduction/gradient-repaired.json \
  1110100100101011101010101110000000 \
  --inputs reference/grammar \
  --metadata reference/interval/instruction-metadata.json \
  --output results/state_reduction/gradient-last-zero-leaf.json
```

It is leaf 2337, a decrement of logical register 1, with old source path
`11101001001010111110000000`. Both zero and positive interval guards are
admitted. The mapper checks equality of all 6460 ordered source leaf labels.
This static correspondence is separate from dynamic RM bisimulation.

## Optional routing searches

All searches use the same input pair and, when specified, the 54-row
bootstrap lock. They are time-bounded heuristics. Proposal counts depend
on the machine's speed; they are not counts of distinct grammars or an
exhaustive search certificate. Each output retains the chosen rules,
caller routes, source properties and seed.

The input generator is optional because its exact output is included:

```sh
python3 -B code/state_reduction/prepare_route_inputs.py \
  --inputs reference/grammar \
  --bootstrap-lock reference/bootstrap/bootstrap_lock.json \
  --output-dir inputs/state_reduction
```

The first version proposes associations, route retargeting and newly
synthesized router-only words. Its first two recorded 600-second seeds
omit bootstrap locks; the third applies them.

```sh
g++ -O3 -std=c++17 code/state_reduction/anneal_routes_v1.cpp -o anneal_routes_v1
./anneal_routes_v1 inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-free-20261018.json 600 20261018 127
./anneal_routes_v1 inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-free-635312.json 600 635312 127
./anneal_routes_v1 inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-locked-247019.json 600 247019 127 inputs/state_reduction/bootstrap-lock54.txt
```

Version 2 also proposes any split whose two children are already active.

```sh
g++ -O3 -std=c++17 code/state_reduction/anneal_routes_v2.cpp -o anneal_routes_v2
./anneal_routes_v2 inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-cut-177246.json 600 177246 127 inputs/state_reduction/bootstrap-lock54.txt
```

The flat scanner objective is `K + max(0,zeros-6)`. Its source file
is preserved to identify the experiment precisely, although the graded
objective below gave substantially more informative progress.

```sh
g++ -O3 -std=c++17 code/state_reduction/anneal_routes_scan.cpp -o anneal_routes_scan
./anneal_routes_scan inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-scan-618712.json 600 618712 128 inputs/state_reduction/bootstrap-lock54.txt
```

The graded objective is `K + 0.1*bad`, where `bad` counts expanded AST nodes
whose leading zero run exceeds 6. Maximum run 7 and depth 64 remain hard guards.
Its result has a fourth `properties` component giving this bad-node count.

```sh
g++ -O3 -std=c++17 code/state_reduction/anneal_routes_scan_gradient.cpp -o anneal_routes_scan_gradient
./anneal_routes_scan_gradient inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-gradient-761906.json 600 761906 128 inputs/state_reduction/bootstrap-lock54.txt
```

The frozen two-bad-node checkpoint is followed by a deterministic finite beam
search. It produced the one-bad-node object used above.

```sh
python3 -B code/state_reduction/repair_scanner_grammar.py \
  inputs/state_reduction/gradient-repair-seed.json \
  --inputs reference/grammar \
  --lock inputs/state_reduction/bootstrap-lock54.txt \
  --output results/state_reduction/gradient-repaired.json --depth 8 --beam 50
```

The final version resumes from the 129-rule zero 6 graph and keeps zero 6 as a
hard constraint while seeking 128 rules. Its seed format contains explicit
rules and caller roots; the old input grammar is retained separately for
source-AST reconstruction fallbacks.

```sh
g++ -O3 -std=c++17 code/state_reduction/anneal_routes_zero6.cpp -o anneal_routes_zero6
./anneal_routes_zero6 inputs/state_reduction/route-grammar.txt inputs/state_reduction/route-constraints.txt route-zero6-129177.json 600 129177 128 inputs/state_reduction/bootstrap-lock54.txt inputs/state_reduction/gradient-zero6-k129-resume.txt
```

## Successful 245-state candidate: independent verification

The frozen final grammar is `results/state_reduction/candidate-zero6-k128.json`.
It has 128 rules, maximum zero run 6 and depth 51. The separate realization has
245 states after removing the old scanner role 74; its numeric label 74 is
reused for a sequence helper. Run:

```sh
python3 -B code/state_reduction/check_route_grammar.py results/state_reduction/candidate-zero6-k128.json --inputs reference/grammar --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt --output results/state_reduction/zero6-k128-audit.json
python3 -c 'import gzip,pathlib; pathlib.Path("candidate245-literal-cases.txt").write_bytes(gzip.decompress(pathlib.Path("inputs/state_reduction/candidate245-literal-cases.txt.gz").read_bytes()))'
g++ -O3 -std=c++17 code/state_reduction/check_literal_cases.cpp -o check_literal_cases
./check_literal_cases candidate245-literal-cases.txt
python3 -B code/state_reduction/check_candidate_boot.py --table reference/candidate245/machine_old.tm --baseline-bootstrap reference/bootstrap/bootstrap.json --output results/state_reduction/candidate245-independent-boot.json
```

The expected results are 8385 passing finite literal cases, maximum 2686 moves
per case, all 490 transition rows exercised, and exact two-interpreter blank
agreement after 407915 moves. Regenerate the final fixtures as follows:

```sh
python3 -B code/state_reduction/transfer_instruction_metadata.py --program reference/source/Prog254.v --sites reference/candidate245/sites_logical.json --metadata reference/interval/instruction-metadata.json --output candidate245-instruction-metadata.json
python3 -B code/state_reduction/make_resource_merge_cases.py --metadata candidate245-instruction-metadata.json --literal-helper reference/literal/check_literal_instructions.py --table reference/candidate245/machine_old.tm --output candidate245-literal-cases.txt
```

Before transferring any fixture, this checks all 6460 ordered instruction
labels and arguments against an independent parse of `Prog254.v`.
`routing-search-summary.json` records the seven search runs, code and result
hashes, and discovery seed. `candidate245-independent-boot.json` pins the
exact old-label table and all 351 final one-cell positions.

A second pair-merge sweep was run on the verified 246-state zero 6 intermediate,
using its remapped source paths and the same recurrent tape resources. It
also had zero full survivors across 120540 recipes (53 passed probes). Its
compressed fixtures and summary are preserved under `zero6-merge/`. This
negative result did not prevent the subsequent successful grammar reduction.

Re-run that intermediate-table merge sweep with the same compiled binary:

```sh
python3 -c 'import gzip,pathlib; pathlib.Path("zero6-merge-cases.txt").write_bytes(gzip.decompress(pathlib.Path("inputs/state_reduction/zero6-merge/resource-merge-cases.txt.gz").read_bytes()))'
./resource_merge_search zero6-merge-cases.txt
```

As above, the sweep writes its summary in the current directory; use a separate
working directory if retaining both freshly generated sweep summaries.
