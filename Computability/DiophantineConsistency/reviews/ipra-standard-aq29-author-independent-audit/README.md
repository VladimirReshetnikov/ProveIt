# Independent audit of the standard-iPRA AQ29 author extension

[`audit.py`](audit.py) independently checks the recorded single-author
[standard-theory trial](../ipra-standard-aq29-author-trial/README.md). The
second invocation exited 0 in tool session 9522; its
[receipt](receipt.json) has SHA-256
`bb60b4f4c9f8904047c3f825da64de152cca52e37006e524be1248cbcb8eedcd`.
The [terminal observation](terminal-observation.json) preserves the actual
exit and output. An earlier invocation printed PASS and produced identical
receipt bytes, but its outer exit code was not captured; it is not counted as
an observed zero-exit run.

The audit rehashes all 1,210 parent source, output and log rows; 13,150
recorded direct companion paths; all 1,540 Foundation artifacts; and all
12,100 overlay companion paths, including the 1,210 present per-file links.
It checks the six exact additional source blobs against their pinned Git
commit and packet copies, their recorded direct inputs and actual output
objects and logs, and the four exact endpoint diagnostic names. The selected
consistency result is the Gödel–Gentzen translation of Foundation's chosen
ZFC consistency sentence; it does not identify arbitrary proof codings.

This is a point-in-time **author-only artifact and recorded-input audit**, not
another Lean execution or a matched peer replay. The parent recorded 15
workspace-source drifts. The Foundation build wrapper's outer exit was not
observed; package-transitive, dynamically loaded and between-observation
dependencies remain outside this audit. The independent audit does not prove
the correctness of a general textbook-iPRA identification or assert
consistency of ZFC.
