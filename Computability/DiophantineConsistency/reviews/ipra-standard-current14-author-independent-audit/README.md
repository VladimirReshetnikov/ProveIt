# Independent audit of the fourteen-variable standard-iPRA author extension

[`audit.py`](audit.py) independently checks the single-author
[fourteen-variable standard-theory trial](../ipra-standard-current14-author-trial/README.md).
The audit actually exited 0 in tool session 40315; its [receipt](receipt.json)
has SHA-256 `624e2f44f4d313ba09ca8d697773620c27f76e53d501add38468b9767b8c0272`.
The [terminal observation](terminal-observation.json) records the exit and
stdout.

The audit rehashes all 1,210 parent source, output and log rows; 13,150
recorded direct companion paths; all 1,540 Foundation artifacts; and all
12,100 parent-overlay companion paths, including 1,210 present per-file
links. It checks all 16 additional source blobs against their pinned Git
commit and packet copies, their recorded direct inputs and actual outputs and
logs, and the four exact standard-theory endpoint diagnostic names. Those
diagnostics report Lean metatheoretic axioms; they are not extra axioms of the
object theory. The selected consistency result concerns Foundation's particular
proof predicate and its Gödel–Gentzen-translated source sentence.

This is an **author-only point-in-time artifact and recorded-input audit**, not
another Lean execution or a matched peer replay. The parent recorded 15
workspace-source drifts, and the extension is a historical hybrid. This audit
does not establish that its fourteen-variable literal is identical to the
current `equation.pdf`. The Foundation build wrapper's outer exit was not
observed; package-transitive, dynamically loaded and between-observation
dependencies remain inherited. The audit neither identifies arbitrary proof
codings nor asserts consistency of ZFC.
