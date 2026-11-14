# Bounded local quotient synthesis

These programs search a specified local replacement family. A negative result
is **not a lower bound on all Turing machines**.

`partial_contexts.txt` describes PA196. `diagonal199_contexts.txt` describes the
final 199-state diagonal machine. Each file contains the complete relevant
table, protected-state flags, and finite partial tape contexts collected from
all symbolic primitive cases and from the concrete blank-tape startup. A `-1`
cell denotes an unknown bit. The principal window has seven cells to the left
of the head and three cells beginning at the head. The simulation limit is
71 transitions. Any access to an unknown cell rejects a trial.

The programs simulate the *modified quotient*, including a possible return to
the merged state. Replaying only the old table would miss the known U208 fold.
Written bits, head displacement, finite window contents, and successor must
agree with the original local effect. Potential hits require the full symbolic
verifier and exact startup before acceptance.

## Build

With a C++17 compiler:

```bash
g++ -O3 -std=c++17 recursive_fold.cpp -o recursive_fold
g++ -O3 -std=c++17 recursive_two.cpp -o recursive_two
g++ -O3 -std=c++17 recursive_wide.cpp -o recursive_wide
```

## Run the main 16-mode search

For PA196, run these five commands. The first tests the bit-preserving,
left/left mode. The other four split the remaining 15 write/direction modes
by their mode number modulo four.

```bash
./recursive_two partial_contexts.txt hits_two.txt > two.log 2>&1
./recursive_wide partial_contexts.txt hits_wide0.txt 0 > wide_0.log 2>&1
./recursive_wide partial_contexts.txt hits_wide1.txt 1 > wide_1.log 2>&1
./recursive_wide partial_contexts.txt hits_wide2.txt 2 > wide_2.log 2>&1
./recursive_wide partial_contexts.txt hits_wide3.txt 3 > wide_3.log 2>&1
```

For Diagonal199, replace the input by `diagonal199_contexts.txt` and use distinct
output filenames. The supplied logs have prefix `diagonal199_`.

The completed PA196 runs tested 5,650,476,975 parameter choices with zero hits.
The completed Diagonal199 runs tested 6,176,511,792 with zero hits. Parameter
choices can encode duplicate quotient machines, so these are not counts of
distinct Turing machines.

## Smaller inherited-row families

```bash
./recursive_fold partial_contexts.txt hits_inherited.txt
./recursive_fold partial_contexts.txt hits_one_new.txt extended
```

The first tries inherited replacement rows; the second permits one newly
synthesized row. The supplied report records their negative results on PA196.
The source includes the exact pair ordering, protected-state rule, and
identical-context prefilter. No claim extends beyond those restrictions.

## Regenerate contexts

From the archive root:

```bash
python3 verification/search/build_contexts.py pa196 /tmp/pa196_contexts.txt
python3 verification/search/build_contexts.py diagonal199 /tmp/diagonal199_contexts.txt
```

The outputs reproduce the corresponding checked inputs. The generator imports
the portable symbolic runtime and records all its primitive cases, then the
literal startup. These contexts are sufficient for this finite search method;
they are not a reachability characterization of the actual infinite run.
