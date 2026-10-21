# Cancel a completed run prefix

`seg_hn` now follows from the existing `seg_run`: execute the segment once, then remove that successful prefix from the halting run. The general `hn_after` lemma records the exact remaining length. Its only obstruction is a halt leaf, which has no outgoing transition (`atHalt_step`). This replaces the second induction over segment syntax.

Every existing declaration statement and executable definition is unchanged; the original `hn_step` wrapper is byte-identical. `RMBisim.lean` decreases from 555 to 544 lines (22,419 to 21,643 bytes), including the two reusable lemmas. The proof is handwritten and has no source producer.

The isolated final candidate and two explicit API clients passed Lean with zero warnings. Four reports for the old and new modules are identical, using only `propext` and `Quot.sound`. [comparison.json](comparison.json) and [api-comparison.json](api-comparison.json) bind those checks. The archive member `source.diff` preserves the exact edit.

[execution.tar.gz](execution.tar.gz) preserves sources, runners, raw logs and records, including the initial elaboration failure and the intermediate redundant-parameter warning. [index.json](index.json) binds every member. Compiled objects are excluded. These isolated checks precede the separate combined phase-four endpoint check.
