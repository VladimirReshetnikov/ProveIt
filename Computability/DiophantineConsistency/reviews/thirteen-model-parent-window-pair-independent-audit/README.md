# Independent 24-module window/rank suffix artifact audit

The read-only [audit](audit.py) of `a4e5d28fc7` exited 0 in session 35035;
its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
bind the result. It checked the exact builder bytes at the recorded launch
HEAD, author outer session 9976 exit 0 and final receipt hash, all 48 compiled
source/object/log rows and direct-dependency exits, both inherited 70-object
and 20-object prefix overlays, and all 710 present-or-absent companion
guards. It independently reconstructed the 24-module source-declared closure
from the pinned 44-source snapshot, excluding the audited prefix. Sibling
source, object and log hashes match. The 48 compiler logs were copied
byte-for-byte from the temporary artifact tree into this audit's `logs/`
directory as `.txt` files; their hashes are checked against the paired
receipt. No Lean compilation was rerun by this audit.

Each sibling has six linter warnings: two suggestions to use `simp` rather
than `simpa`, one no-op `simp` and one unreachable tactic in
`ArithmeticBinaryCarry`, and one unused-variable warning each in
`ArithmeticCyclicWord` and `ArithmeticWindowCarry`. The logs contain no
reported error or `sorryAx`. They print **no axiom reports**, so this result
does not provide a complete axiom inventory. The author reports a clean
initial native-loader environment; this review did not independently observe
the original process environment. The launch HEAD is recorded, but the driver
does not continuously enforce HEAD or input immutability.

This is an audited artifact and direct-guard result for the 24-module suffix,
not an actual-zero caller theorem, a 69-operation converse, a fixed-port
consistency calibration or an iPRA proof. Sampled leader RSS and disk checks
are not hard quotas or whole-process-tree measurements; observed 4096-byte
samples are not reliable peak usage. Package-transitive/dynamic ancestry and
the original Foundation outer-wrapper exit remain inherited qualifications.
