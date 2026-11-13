# Equal-length nine-variable CURRENT2011 endpoint replay: stages 77–81

The guarded equal-length-root verification replay completed
`ModelCarrierScaled`, `ModelCarrierSyntax`, `ModelCarrierCurrent`, the
`IPRANineCurrent` endpoint and its `IPRANineChecks` axiom-report client. The
retained audit checks the complete prefix 1–81: each author/verification
output is byte-identical or becomes byte-identical by replacing its single
embedded source pathname with the same-length verification pathname. Any
differing direct-input hash must correspond exactly to a previously checked
predecessor. Direct and companion guard records match after mapping only those
verified predecessor hashes and normalizing overlay roots; sources and
complete compiler logs match under source-path normalization.

The stage-80 endpoint and stage-81 client objects are byte-identical; stage
80 imports a different-hash stage-70 object which passed the stated whole-file
pathname comparison. All 15 source-named axiom reports in the stage-81 log
match and list only `propext`, `Classical.choice` and `Quot.sound` as Lean
metatheory dependencies, not object-theory axioms. This remains a scoped
byte/source-path-normalized replay, not an assertion that every raw object
hash matches or a proof of Lean's binary format.

These five stages overlapped the compact stage-95
`ArithmeticDagControlPerm222` retry, following the explicit two-Lean-process
resource decision. [`run.py`](run.py) starts one guarded stage at a time,
checks `/proc/meminfo` `MemAvailable` before each, and samples memory and Lean
processes every two seconds. Each stage has samples showing both processes;
at most two Lean processes were observed and the lowest sampled
`MemAvailable` was 17,474,924 KiB. [`check_overlap.py`](check_overlap.py)
rechecks the retained samples. They are not continuous monitoring or a
cgroup-limit proof.

[`audit.py`](audit.py) and [`capture.py`](capture.py) retain the full-prefix
comparison, sources, receipts, dependency listings and compiler logs under
[`observations`](observations/). The previous [1–76 prefix](../nine-variable-ipra-equal-length-stages-72-76-overlap/README.md)
is a separate frozen packet. Author warning baselines and historical
project/package/dynamic ancestry remain inherited, and no file or PDF
transcription is proved. Live `/tmp` overlays are needed to repeat the check.
