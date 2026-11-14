U213 from U214 by bypassing an entry path
========================================
Certified result: 213 working states, 426 binary transitions, separate halt.
Native edits: 180/read1 goes to167; 172/read0 goes to67; delete112.
The report proves PA-provable halting equivalence with the pinned U214,
preserving its Con(U) endpoint. The source and theory are unchanged.
This is a conventional mathematical proof, not a new proof-assistant certificate
or a global minimality claim.

Baseline source commit: 24503cb019c7509ea229e80ef9b7a11a1501203c.
The U214 selection ledger preserves all original file hashes. Six large
runtime/startup trace dumps and the nested U218 ZIP are omitted; a compact
U218/U222 dependency selection is supplied separately. New checks reconstruct
all primary symbolic cases and the blank initialization.

Python standard library only. From a fresh extraction run:
  python3 checks/check_release_manifest.py
  python3 checks/replay.py
The latter runs16commands, including both5109-case symbolic runtime checks.
Do not run replay under -O: safe optimized subcommands are checked explicitly.
Replay writes new receipts, so check the original manifest before replay.
The baseline Python files are source evidence; replay uses independent scripts
and exact hash-bound runtime helpers authored in earlier construction work.

For a full TeX installation, run pdflatex twice on report.tex. The build_local.sh
helper accommodates this workspace's read-only TeX configuration with a local
format; build/report.pdf is the rebuilt output. The archived report.pdf is the
delivered report. The separate final delivery receipt records sealed replay and
page-image/text comparison of the unchanged archive.
