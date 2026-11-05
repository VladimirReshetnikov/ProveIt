# Cleared integer representation and its iPRA sentence

The client explicitly chooses `clearedExpression` as the existing current14
integer expression at the actual ports. `cleared_eval` checks that this
expression evaluates to the checked normalized 65-row graph at every
integer valuation. It then builds `clearedNoZero` from that expression's
positive shift and proves `clearedNoZero = noZero14` **definitionally**
with `rfl`. Finally `cleared_ipra` proves that standard iPRA derives the
equivalence between this integer-language no-zero sentence and the
intuitionistic negation of the mapped native ZFC-refutation predicate.

The preceding actual-port result connects this integer expression to the
64-row rational evaluator **externally**, through equality of ordinary
integer/rational evaluations. This client does not construct a rational
object-language term, prove an iPRA sentence containing rational constants,
or reduce the normalized integer expression below 65 operations. The term
is selected as the existing normalized syntax and then bound by the checked
65-row evaluation theorem; it is not the output of a newly formalized
rational-expression clearing algorithm.

Attempt01 passed with Lean and runner exit 0, no warnings or `sorryAx`;
all three axiom reports are `[propext, Classical.choice, Quot.sound]`.
The run used `-M2800`, 120 seconds, sampled 3.5 GiB process-group RSS and
10 GiB available-memory limits, nice 19 and idle I/O. It took 2.453 seconds,
peak sampled RSS was 2,840,612,864 bytes and minimum available memory
18,786,930,688 bytes. Direct provider guards and predecessor receipts were
stable. The outer session 52395 was independently observed to exit 0 and
is recorded in `observations/attempt01/outer-terminal.json`.
Transitive/dynamic provider ancestry and sampled monitoring remain limits.

The output object is
`/tmp/rational-carrier64-cleared-ipra-priority-check01/ClearedCurrentIPRA.olean`,
SHA-256 `d895d103bb0a8b888c205c4c7c33bbcdf8a9bbcd735c687475dc6fd96175b1f5`.

| Artifact | SHA-256 |
| --- | --- |
| `ClearedCurrentIPRA.lean` | `1f8e69d01966a3d933ac7d6c12f010b0374831502c1f96f8da5f8afb15fb70d7` |
| `check01.py` | `f9adc7f18ca8fee344c438e7abb75d9729d8bbf495a1e8035c74d3a25efb972a` |
| `observations/attempt01/compile.log` | `cda4a16e1ed9579a3c8bc6380d9f5821f33f29e84b4b46579a427e22713e60d3` |
| `observations/attempt01/result.json` | `57e8509112bf368c21425ab22c4611a269f506a92da7ec9c3e656b3f4e630d8b` |
| `observations/attempt01/outer-terminal.json` | `fbaa7de6b563da8cca95bc219d69e3cf41a6fbb7e1fb0ad5b78a0cb24f6c1126` |
