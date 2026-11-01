# Guarded v3 input for 85 zero-score coding

This packet freezes the source, generated checks, scripts and direct-input
manifest for a focused replay of `AdaptiveGap85ScoreCoding`. It gates on the
separately reproduced Cantor dependency and its truthful observed-exit receipt.
The manifest fixes the source and Checks bytes, Lean executable, exact
score-parent namespace entries and realpaths, and the original score workspace
source. It guards 398 provider project entries, 3,980 provider companion
presence/absence candidates, 300 direct score-module candidates, and the 500
Cantor direct-input candidates from the repair packet.

`replay.py` creates a private project overlay, verifies its entire entry and
realpath inventory, and checks `lean --deps` for both the source module and
its generated Checks module before compilation, after the first module and
after the second. The Checks module's future source object must initially be
absent and must then resolve to the newly compiled object; main-source
dependencies must resolve to the selected `AdaptiveGap85BalanceLeast` and
reproduced `ArithmeticCantor` objects. Each audit also rechecks source and
Checks bytes, the provider inventories, sidecar/shadow absences, Cantor gate,
and all recorded input hashes. Full logs and axiom checks are required.

`compare.py` matches two completed runs, normalizing only their private-root
paths, and freezes both complete source, object, log and state records.
`independent_audit.py` separately rechecks those records, the entire retained
private overlay and current direct Lean resolutions. These scripts are to be
run with ordinary Python; `python -O` disables their assertions and is not a
valid verification run. Host-specific paths and historical parents in the
manifest must be available to reproduce it.

This is a direct-dependency audit, not an independent rebuild of transitive
project/package source-to-object or dynamic ancestry. The original Cantor
provider failed later on a different module; its successful Cantor and Code254
rows and direct-input reproduction are explicitly documented in the linked
repair packet. Earlier v2 score replays remain qualified preliminary evidence.
