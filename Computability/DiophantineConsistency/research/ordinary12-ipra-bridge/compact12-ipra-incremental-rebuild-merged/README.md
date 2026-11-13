# Merged-root compact/iPRA exploratory rebuild

This author-side resumable build uses the 441-source pin, the checked
serialized-import inventory, and the compact-first selected provider overlay.
It materializes a fresh library root consisting of symlinks to every selected
object and writes rebuilt omitted objects as regular files in that same root.
This is necessary because the earlier two-root attempt resolved a dependency
to a nonexistent file in the first root; see the sibling
`compact12-ipra-incremental-rebuild` failure record.

The first batch ran five source modules in pinned dependency order. All five
Lean processes exited 0 without warnings or `sorryAx`; their copied sources,
exact direct dependency lists, companion guards, logs, receipts and output
hashes are under `observations/stage-01` through `stage-05`. After the batch,
the runner again verified all pinned sources, selected overlay files, merged
symlinks, and rebuilt outputs, and exited 0 with `completed: 5, total: 59`.
The first batch's exact runner is retained as `observations/batch01-runner.py`,
SHA-256 `676f96efdb48de6afe41ebb15f068df521b49113acd995b6eacd78de0fe1857b`.
The current `run.py` also revalidates previous stages' full direct-dependency
and companion guards on resume; that addition has not yet been exercised.

This is not an iPRA endpoint or an independently paired replay. The 59-module
cone is based on the checked `DiophantineConsistency.*` source/object import
analysis; other namespace, package, dynamic and transitive ancestry remain
unverified. A successful prefix cannot certify the remaining stages or the
subsequent compact symbolic bridge. All filesystem guards are point-in-time.
