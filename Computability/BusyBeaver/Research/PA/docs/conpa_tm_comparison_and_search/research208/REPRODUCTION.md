# Reproduction guide for the U208 audit branch

**Final result: no accepted machine with fewer than 196 working states.**
The JSON files with `195` in their names are explicitly rejected diagnostic
candidates. See `STATUS.json` and `AUDIT_NOTES.md` for the claims and limits.

## Smallest self-contained new result

The finite source abstractions require only these four files:

- `source_boolean_input.txt`
- `boolean_source.cpp`
- `ternary_source.cpp`
- `quaternary_source.cpp`

The input is the resolved 3,812-instruction PA196 graph. Its first line gives the
instruction count and clean entry ordinal 25. Each subsequent line is
`opcode register zero_destination positive_destination`, where opcodes 0, 1, 2,
3 mean increment, decrement, jump, halt. A jump uses the last destination; unused
fields are ignored. The initial register assignment is R0 = 2 and all others 0;
the Boolean and ternary abstractions conservatively abstract that assignment.

From this directory, run:

```sh
g++ -O3 -std=c++17 boolean_source.cpp -o boolean_source
./boolean_source source_boolean_input.txt
g++ -O3 -std=c++17 ternary_source.cpp -o ternary_source
./ternary_source source_boolean_input.txt ternary_source_values.txt
g++ -O3 -std=c++17 quaternary_source.cpp -o quaternary_source
./quaternary_source source_boolean_input.txt quaternary_source_values.txt
```

Expected closure sizes are 274,880; 4,455,507; and 32,947,398, respectively.
The Boolean abstraction excludes source ordinals 3774 and 3775. Both refinements
also exclude ordinal 8. Zero-only decrements are 3773 in the Boolean case, and
7 and 3773 in both refinements. The supplied `.log` files record those outputs.
The optional values file records, for each source ordinal and register, a bitmask
of abstract value classes encountered. These are computational closure results;
a separate abstract-transfer soundness argument is required to use them as a
PA proof. They do not assert nonhalting of the complete machine.

## Reachability-restricted transition folding

Required new files:

- `reachable_fold_prepare.py`, `reachable_fold_search.cpp`,
  `reachable_fold_validate.py`
- `ternary_fold_prepare.py`, `ternary_fold_validate.py`
- `prepare_tail_inputs.py`, `tail_fold_all_coupled.cpp`

The Python files import the existing exact symbolic executor `core.py` from the
prior archive `pa_tm_research_2026-11-13.zip`. The packaged dependency is under ../support; the source extraction originally had this layout:

```text
pa_tm_research_2026-11-13/pa_tm_research_2026-11-13/
  work/optimize196/core.py
  sources/BusyBeaver/PA196/Conjugacy.lean
  sources/BusyBeaver/PA196/Program.lean
  sources/BusyBeaver/data/pa196.tm
```

Those four extracted files suffice for the native-fold and scanner checks here.
The full upstream source is useful for independently reviewing the oracle lemmas.
It is not necessary to include the generated local-window files in a small
archive, because the prepare scripts deterministically recreate them.

```sh
python reachable_fold_prepare.py
g++ -O3 -std=c++17 reachable_fold_search.cpp -o reachable_fold_search
./reachable_fold_search reachable_fold_input.txt > reachable_fold_options.txt
python reachable_fold_validate.py
python ternary_fold_prepare.py
./reachable_fold_search ternary_fold_input.txt > ternary_fold_options.txt
python ternary_fold_validate.py
python prepare_tail_inputs.py
g++ -O3 -std=c++17 tail_fold_all_coupled.cpp -o tail_fold_all_coupled
./tail_fold_all_coupled tail62_fold_input.txt
./tail_fold_all_coupled halt68_fold_input.txt
```

The first native-fold search omits precisely the three impossible contracts
3773-positive, 3774, 3775. The second additionally omits 7-positive and 8.
All retained primitive contracts still quantify over arbitrary register-file
values, beyond the omitted branches. The two local-action screens each use a
20-cell radius and 100 native transitions; both produce 55 candidate state pairs,
and every concrete quotient fails a retained contract.

Each coupled search permits both rows of one merged state to change, including
recursive visits to that state. It tries 105,720,832 row pairs across 172 partner
controls, within a 20-cell radius and 240 transitions. Both have zero local
survivors. A local success would still require complete symbolic validation,
register-oracle compatibility, and a literal blank-start check. These finite
search bounds are not lower bounds on possible machine sizes.

## Scanner shortening witness

`scanner_test.py` uses the same four-file symbolic-executor dependency. Running
it reconstructs `scanner_results.json`. Removing the last one or two zero-counter
states already fails a retained source contract. Removing the last three states
causes the blank-start machine to halt after 699 transitions. The latter is a
concrete rejection witness, not merely failure of a sufficient verifier.

## Comparison and diagnostic rotations

Keep `fresh_comparison.json`, `AUDIT_NOTES.md`, and the archived exact comparison
script if including the complete comparison. The nine audited final U208 tables
fall into two rooted labelled graph classes, not nine distinct optimizations.
The native 172/211 eliminations are the same history fold after renaming.

For compact documentation of the strongest unsuccessful rotations, retain:

- `alt_first_rotation195.json` and `alt_scanner_repair.json`
- `alt_only_router195.json` and `alt_only_router195_ideal.json`
- `alt_repair195_2.json`

An `ideal` result replaces the shared2037 control by an oracle that consults the
complete source prefix. It is a diagnostic device and is not a transition table
for a valid Turing machine. The first rotation has an additional seven-zero
address issue; the four-rotation version leaves only the unresolved history
router. Source CFG agreement and a 195-row-pair count therefore do not establish
a successful reduction.

## Suggested compact evidence set

Include the files named above, `STATUS.json`, and these small logs/results:

- `boolean_source.log`, `ternary_source.log`, `quaternary_source.log`
- `reachable_fold_prepare.log`, `reachable_fold_search.log`,
  `reachable_fold_validate.log`, `reachable_fold_result.json`
- `ternary_fold_prepare.log`, `ternary_fold_search.log`,
  `ternary_fold_validate.log`, `ternary_fold_result.json`
- `tail62_fold_all.log`, `halt68_fold_all.log`, `scanner_results.json`

Generated executables, large local-window files, and progress logs are optional.

In this combined archive, execute Python research scripts from the archive root, for example `python research208/ternary_fold_prepare.py`. Their source locator has been redirected to `support/`. C++ examples above may still be run from this directory.
