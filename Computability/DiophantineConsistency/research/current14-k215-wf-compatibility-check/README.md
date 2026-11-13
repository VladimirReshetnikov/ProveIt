# K215 proof-refactored original module guard

This client recompiles the 18-stage helper assembly and `RMNormalizedBisim`, then checks the separate proof-refactored `KSource215Data` draft. The draft adds a helper import, replaces the costly `wfCheck222` proof, and appends report commands. It preserves the original project file and does not claim a byte-identical rebuild. Definitional equality is untested until the guarded Lean run passes.

Caps remain `-M3600 -j1`, 4 GiB sampled child RSS, 180 seconds per child, 10 GiB host available memory and a 5.1 GB sampled disk stop. The six-hour budget triggers a stop; forced receipt and cleanup, including log hashing, may finish later. No existing outputs are deleted. Package/dynamic ancestry and the full coherent endpoint remain separate.

Controls and preflight do not run Lean. A run requires independent prelaunch review and an allocated Lean slot.

Attempt01 passed: outer session 77870 exited 0, all 20 stages and postflight passed. The [independent terminal audit](../../reviews/current14-k215-wf-compatibility-terminal-independent/) checked the source refactor, producer routes and three original-namespace axiom reports. The full coherent endpoint rebuild remains separate.
