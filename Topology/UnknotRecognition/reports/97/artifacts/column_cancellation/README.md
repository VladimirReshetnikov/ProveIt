# Column-cancellation evidence

`column_cancellation_20261012.json` contains the complete paired benchmark
record from CPython 3.12.14, including all five timing samples, medians,
structural operation counts, source identifiers, and validation outcomes.
`column_cancellation_tests.txt` is the saved 36-test focused integration log.

The full 106-case supplied-cut experiment agreed on every status and census:
78 COMPLETE and 28 INCONCLUSIVE. All 156 successful old/new certificates
independently replayed. The whole-query medians were 36.515 seconds before
and 36.211 seconds after, so there was no material whole-query timing gain.
The aggregate prepared-core experiment measured a small-input regression.
Large synthetic matrix gains concern only the specified kernel and replay.

The benchmark source, exact baseline modules, resulting native files, and
portable reproduction instructions are in `../../integration/`. Apply that
overlay to the pinned ProveIt checkout before rerunning the benchmark.
