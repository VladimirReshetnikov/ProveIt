# Phase26 Lean evidence

The full check passes **230 providers**: 215 project modules and fifteen unchanged
typed clients, with **56 fresh / 174 exact phase25 reuses**, plus **two fresh
endpoint audits**. All selected logs have zero warnings; the exact ordered
93 client / 5 WFTheory / 10 audit reports match. All nine site batches compile
fresh. Thirteen boot chunks and sixteen source-forward batches retain exact
accepted phase25 bindings.

The [terminal result](result.json) has SHA-256
`03131039c9530549ce64ad38089947629f5dea14dd7e974050437fa513d32eb2`.
The [plan](check-plan.json) has SHA-256
`0d4dc2c41f7f83a30f64ae28c7d0441b77c13dd61b94fa2a0b2eb0bab8f1eb89`.
[Actual readback](result-review.json) verifies 1,328 owner inputs, 171 present pins
and sixteen absences, with 227 original raw provider records and three disclosed
inherited absences. No missing record is reconstructed. The
[independent actual peer](../integration/actual-peer.json) passes.

The [capture](capture.json) and
[independent archive review](../integration/capture-review.json) pass.
It stores **724 blobs / 1,142 logical entries / 1,069 source paths / 830 raw files**,
with two explicitly failed focused contexts. The archive is 1,570,297 bytes,
SHA-256 `fc54852716d164963d84db4eddbc4fa0fef4fd2073adabd9107d559de1fe5a80`.
Three empty historical lock files remain required frozen input metadata; the
passing focused run's lock is omitted. No proof objects or previous archive are
recopied. The exact eleven-file [phase25 leaf](../../phase25/lean/README.md)
remains external and unchanged.

The final focused check passes twenty providers (eleven fresh / nine reuses),
zero warnings. Its two failed predecessors and repairs remain preserved; a
focused result never supplies the full-run reuse basis. The separate five-line
prefix proof cut is uncompiled research and excluded from production savings.

Controls retain pinned Lean 4.32.0 and the owned supervisor/global lock,
`-j1`, `LEAN_NUM_THREADS=1`, `-M12288`, 120-second ordinary/audit limits and
900-second site/forward limits. Source, object, dependency, log, toolchain and
input bindings are checked before and after the run. The observed outer duration
is 1,350.83 seconds; no speed comparison is claimed.

The [index](index.json) binds inert raw evidence and owned controls to their
recorded paths. No captured code is executed by capture or review. Use the
maintained [Lean reproduction driver](../../../lean/README.md) for a fresh source
build. The machine remains 215 states; the internal PA endpoint and minimality
remain open.
