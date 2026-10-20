# Exact obstruction for every initial state

The literal [217-state table](core217.native.tm) is accepted K218 with state301 removed and three rows changed: `87/0 = 0 R 88`, `88/0 = 0 L 51`, `51/0 = 0 R 122`. It has 434 transitions. Changing only its declared initial working state cannot repair its blank startup: **all 217 starts have explicit infinite zero-ray proofs**.

For each start, the [complete finite witness](verification.json) reaches a nonhalting state `q`, head `h`, and finite set of one cells. The scanned cell is zero, the zero row returns to `q`, and its direction points into a half-line containing no ones. One transition preserves these conditions because the new write lies behind the moving head. Induction gives an infinite run in the same state. Consequently none of these starts reaches the required computation; this does not rule out modifying another row or a different 217-state machine.

The [C++ discovery](search.cpp) scanned the 216 starts other than0 in 0.001213 seconds, with 1,702 transitions altogether and no bound reached. The earlier start0 trace contributes85 transitions. All finite prefixes are at most85 steps. The configured limits were one million transitions per start,110 seconds internally,120 seconds externally. The result is stronger than a bounded failure because each terminal observation has the inductive ray certificate above.

The original [Python verification](verify.py), original [result](verification.json), JSONL streams, raw logs, exact table, and [provenance](provenance.json) are preserved unchanged. The old verifier includes historical absolute paths and a hash of the unshipped compiled discovery executable. Use [replay.py](replay.py) for portable reproduction. It independently simulates the complete tape for all217 prefixes, checks every ray obligation, binds the literal table to the accepted K218 table, and compares the entire preserved start0 trace.

As a positive control, the C++ detector found the accepted K218 frame at312,909 steps: state84, head−5, gap80, logical registers `[3,0,0,0,3,0,0,0,0]`,130 one-valued spares, and277 one cells. The portable Python replay separately verifies that exact complete support, encoding the expected physical register order itself. Its [fresh result](portable-replay.json) passed. These independent implementations share the same author, `drop_contract`; no independent reviewer or proof-assistant check is claimed.

From this directory, write fresh outputs:

```sh
python3 -B replay.py --output /tmp/k217-all-starts-replay-fresh.json
g++ -std=c++20 -O2 search.cpp -o /tmp/k217-start-search-fresh
timeout 120s /tmp/k217-start-search-fresh core217.native.tm 1000000 110 1 511 > /tmp/k217-starts-fresh.jsonl
/tmp/k217-start-search-fresh ../../candidate-k218/k218.native.tm 1000000 110 0 0 > /tmp/k218-start-control-fresh.jsonl
```

The first command replays archived proof witnesses; the latter commands rediscover the216 prefixes and positive control. Historical start0 is included in the portable replay. The literal scanner's always-null `first_other_clean_frame` field is retained as emitted; the separate `observations` list is authoritative. No full symbolic runtime was rerun for the failed217 table.
