# Source preservation and concurrent live-report activity

The before snapshot was captured at 2026-10-04T15:24:54.675013+00:00, after the initial read-only source inspection. The after snapshot was captured at 2026-10-04T15:32:53.244416+00:00. The fresh inspected helper verified the two caller-supplied manifest pins, all 21 listed source packet files, and all 17 audit-manifest entries. Audit entries also matched their recorded modes and mtime_ns.

All 49 snapshotted frozen-source entries were byte-, mode-, and mtime-identical at the two observations. Directories were also checked for mode/mtime equality. Source atimes are outside this requested preservation scope and can change through reading. This is equality of endpoint snapshots, not proof that a tree was continuously static between them.

The live Report70 release was observed separately. It was NOT static across this interval: 49 new file/directory entries appeared under its qa tree, including ROOT_MANUSCRIPT_ACCEPTANCE.json and manuscript-review evidence with rendered pages. The existing qa directory's mtime changed. No other already-existing entry changed its snapshotted bytes, mode, or mtime. These are observed concurrent live-report changes; this worker did not write to Report70 or use its changing QA content as mathematical evidence. The mathematical input is the pinned older source packet and audits.

The complete before/after records and exact changed paths are in evidence/before.json, evidence/after.json, and evidence/preservation-receipt.json. evidence/authenticate_inputs.py is the fresh inspected hashing helper used for both snapshots. It imports no source code and executes no archive programs. The copied dependencies were compared byte-for-byte with their pinned origins before sealing.

The only scientific calculation executed for this continuation is check_static_algebra.py, a fresh static affine integer checker with 408 checks and 44 endpoint-support corner cases. It never evaluates a CA step or source-machine instruction. No upstream/author program, source interpreter, physical/trajectory simulator, saved schedule, or Lean ran. No public mutation occurred.
