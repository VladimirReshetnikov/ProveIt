# Prepared P72 current-base source-snapshot extension

This runner prepares a single ordered build of the 681 source modules outside
the 918 shared current14 base modules in the source-declared P13/P14 closure.
It does **not** merge the previously captured compact objects into the fresh
base. It snapshots each additional source, copies no provider objects, and
places symlinks to the authenticated base outputs in a private project root.
Each stage checks its direct `lean --deps` names, first-provider route,
companion/shadow inventory and source hashes, records a separate row and both
Lean logs, and stops at the first resource, dependency or proof failure.
The final audit rechecks every recorded output and guard, sources, base and
external observations. P13/P14 endpoint axiom reports are whitelisted if
those stages are reached.

The final no-Lean preflight returned exit 0 in actual session 26830; its
[output](preflight-pass.json) SHA-256 is
`49356de344c045f2b949843df4bc6066c90d215c938b1be629b51dee991d8ac7`.
It checked 918 shared producer/source records, 9,180 base output/absence
slots, 2,647 recorded direct edges and 1,600 external companion slots. The
runner SHA-256 is
`6ff8b344fd852a9b78c7c732f0ea8d477a131725cdf14df14551d14a154f3c7a`.
An earlier preflight passed and a second correctly refused while another
authorized Lean job was active; the point observations are recorded in
[preflight-observations.json](preflight-observations.json). No build has
launched at the time of this preparation.

Each Lean invocation uses `-M4000`, one worker, low priority, a sampled
5-GiB session RSS threshold, sampled 10-GiB host available-memory floor, a
180-second timeout and a 5-GB free-disk precheck. The stable process-handle
monitor refuses an observed descendant; its sampling can miss transient
spikes or escaped processes. The saved per-stage rows and progress file are
not by themselves a separately observed outer process exit. The source and
direct guards do not certify full package-transitive/dynamic import ancestry
or exclude changes between observations. A successful narrow combined-import
probe does not guarantee this longer extension will compile.
