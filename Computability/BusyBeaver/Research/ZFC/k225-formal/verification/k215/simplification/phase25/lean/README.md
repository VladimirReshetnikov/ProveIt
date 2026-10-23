# Phase25 Lean evidence

The full selected build passes **230 providers** (215 project modules and fifteen
unchanged typed clients): **110 fresh / 120 exact phase24 reuses**, with **two
fresh endpoint audits**. All selected logs have zero warnings; the full ordered
93 client / 5 WFTheory / 10 audit reports match the frozen plan. All nine site
batches, thirteen boot chunks and six affected clients compile fresh. All sixteen
source-forward batches retain their exact accepted phase24 bindings.

The [terminal result](result.json) has SHA-256
`9532e7d8d09f746c1ec509d09ba8e7eea76f752998a602afd4c2aa6cbdaf0d3c`.
The outer build takes **1,330.62 seconds**, an observed duration with interleaved
serial diagnostic calls, not a performance comparison. The [full plan](check-plan.json)
has SHA-256 `e5a4cfb2e342a944e563ccb76a27a08beb9f653403637681c755161de34fd471`.
It binds 111 present inputs and sixteen absences. [Independent actual readback](result-review.json) passes: 1,259 owner inputs,
111 present pins and sixteen absences. It binds 227 adjacent raw provider records
and discloses three inherited absences (the phase24 basis has twelve). No raw
record is fabricated. The [capture](capture.json) and [independent archive review](../integration/capture-review.json)
pass: **671 blobs / 1,146 logical entries / 1,139 source aliases / 578 raw files**.
The archive is **1,803,613 bytes**, SHA-256
`c97fc3b7db5007217440e1856956a2c98fd56a8abdb2e0c6fa5c08976dc694ba`.

The earlier focused check passes 35 providers (27 fresh / 8 exact reuses) in
42.33 seconds. Its failed first elaboration and the two source repairs remain
archived as diagnostics; neither focused result supplies the full-run reuse basis.
The [direct-profile readback](../integration/calculus-profiles/reduction.json)
accepts only `cons_sub: [propext] → []`, with six unchanged ordered profiles.
The [original equality comparison](../integration/calculus-profiles/original-comparison.json)
remains a FAIL. Both underlying Lean probe calls succeeded with zero warnings;
no recompile was needed to verify this strict axiom reduction.

The runtime uses pinned Lean 4.32.0, the existing supervisor and global lock,
`-j1`, `LEAN_NUM_THREADS=1`, `-M12288`, 120-second ordinary/audit limits and
900-second site/source-forward limits. Timeout and interruption cleanup waits
for the compiler process group. Exact source, object, dependency, raw-log,
toolchain and resource bindings are checked before and after the run.

The eleven files in this leaf freeze the new evidence. The previous
[phase24 leaf](../../phase24/lean/README.md) stays an exact external boundary;
its archive is not recopied. No executable proof objects are shipped. Stored
paths identify the original frozen workspace. Use the maintained
[Lean reproduction driver](../../../lean/README.md) for a fresh source build;
[owned runtime sources](../integration/runtime/build-candidate.py) preserve the
historical controls and their explicit path bindings.

The separate prefix experiment is [research evidence](../follow-ups/decrement-prefix/README.md).
Its three-block result is not full variant coverage or production adoption.
The machine remains 215 states; the internal PA endpoint and minimality remain open.
