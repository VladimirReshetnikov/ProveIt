# Optional bounded runtime searches

These searches found no additional one-state merge. They are not machine
correctness proofs or lower bounds. The accepted PA194C verifier is at the
archive root.

Families A/B are the supplied 67-reader and 68-reader PA194 baselines;
C is the new Combined controller. Native labels are retained because the
search excludes named arithmetic-box controls and starts abstract closure
at native state74.

## Replay source-context extraction

From this directory:

```sh
python3 -B extract_contexts.py A --radius 4
python3 -B extract_contexts.py B --radius 4
python3 -B extract_contexts.py C --radius 4
python3 -B extract_contexts.py C --radius 6
```

Each command replays every symbolic source outcome and exact blank startup,
then records conservative local windows. Independent correlations may be
forgotten, enlarging the context set. Box controls are excluded as merged
controls. These are optional exploratory contexts, separate from the
independent whole-tape acceptance checker.

## Replay the local-action search

With a C++17 compiler, from this directory:

```sh
mkdir -p generated
g++ -O3 -std=c++17 action_merge.cpp -o generated/action_merge
generated/action_merge ../../construction/tables/pa194c.native.tm 4 100 recorded/contextsC/symbolic_patterns_k4.txt > generated/C4.jsonl 2> generated/C4.log
generated/action_merge ../../construction/tables/pa194c.native.tm 6 160 recorded/contextsC6/symbolic_patterns_k6.txt > generated/C6.jsonl 2> generated/C6.log
```

Omit the final context-file argument for conservative all-tape window
closure. Substitute `../../construction/tables/pa194.native.tm` for A,
`inputs/B.native.tm` for B, and their recorded contexts. Every recorded
candidate JSONL is intentionally empty; the paired progress logs show
all194 controls processed.

`recorded/shortscan_C_failures.json` records the113 failing generic source
outcomes after deleting native34 and redirecting its incoming targets to75.
`recorded/shortscan_C_blank.json` records a separate nonhalting two-million-
transition screen. The latter does not validate the shortcut. The search
report explicitly distinguishes failure of the universal source contract
from a theorem about actual blank reachability.

`recorded/mixed_raw_A.json` and `mixed_raw_B.json` record all simple
previous-bit pair opportunities in the two raw tables when fixed readers
are also eligible. None of those opportunities is a mixed fixed/AX pair.
The extended association searches in the neighboring directory reapply
larger detectors to changing source trees.

The input B tables/grammar and the local-action search source are copied
from current Git-bound archives. PROVENANCE.json records their hashes.
