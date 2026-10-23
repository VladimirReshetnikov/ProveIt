# Phase27 Lean evidence

The full check passes **230 providers**: 215 project modules and fifteen unchanged typed clients, with **140 fresh / 90 exact phase26 reuses**, plus **two fresh endpoint audits**. Thirteen clients compile fresh. All selected logs have zero warnings; the exact ordered 93 client / 5 WFTheory / 10 audit reports match. Nine site batches, thirteen boot chunks and sixteen source-forward batches retain their exact accepted phase26 bindings.

The [terminal result](result.json) has SHA-256 `e61268e395962faf774836fe5448dae8b22cd72757b4cc0c9cee7b913363aa70`. The [plan](check-plan.json) has SHA-256 `60b0cd8f5f69ffefd2c024d263b7dda225bd38c208136d9bf29897013fbf4477`. [Actual readback](result-review.json) verifies 1,264 owner inputs, 107 present pins and sixteen absences. The full freeze binds 338 files. The [independent actual peer](../integration/actual-peer.json) also passes.

There are 228 original raw provider records and two inherited absences: `BusyBeaver.Core` and `BusyBeaver.ZFC.FramedWindow`. Rebuilt `FirstOrder.Fol` has a fresh raw receipt. The previous basis’s three historical absences remain disclosed; no record is reconstructed.

The [capture](capture.json) passes. It stores **698 blobs / 1,226 logical entries / 1,221 source paths / 846 raw files**, including the sole passing focused diagnostic and its reviews. The [independent archive review](../integration/capture-review.json) passes. No objects, lock files or previous archive are copied. The exact eleven-file [phase26 leaf](../../phase26/lean/README.md) remains external and unchanged.

The archive is 1,271,215 bytes, SHA-256 `d3ece538b6f4230e36ae8ef23dea265ecd4bdad2eb89587613f0f1b64bf2a284`. The focused check passes 68 providers (56 fresh / twelve reuses), zero warnings and no audits. It supplies no full-run reuse basis. No focused or full kernel invocation failed in this phase. An independent reviewer’s overly strict historical-log parser precheck was corrected as metadata only; the inherited information lines and exact reports remain unchanged.

Controls retain pinned Lean 4.32.0 and the owned supervisor/global lock, `-j1`, `LEAN_NUM_THREADS=1`, `-M12288`, 120-second ordinary/audit limits and 900-second site/forward limits. Source, object, dependency, log, toolchain and input bindings are checked before and after the run. The observed outer duration is 295.86 seconds; no speed comparison is claimed.

The [index](index.json) binds inert raw evidence and owned controls to their recorded paths. Capture and review execute no captured code. Use the maintained [Lean reproduction driver](../../../lean/README.md) for a fresh source build. The machine remains 215 states; the internal PA endpoint and minimality remain open.
