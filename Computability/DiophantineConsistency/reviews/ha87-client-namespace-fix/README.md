# Exact HA client namespace fix

Focused run `/tmp/ha87-focused-validator-rebase-txwf5fe7` failed at `HAAdaptiveFactor87` after 81 verified rows because `ProofEquiv` was not in scope. Its failure state and newly compiled logs are included. Opening `FoundationHADeltaZeroGG` fixes the exact client; a scratch compile against the inherited, pinned-ZF overlay succeeded, and its checks print only `propext`, `Classical.choice`, and `Quot.sound`. This does not authenticate the historical HA, project-object or transitive package source closure, and it is not an independent replay.

This packet records the client and two subsequently merged guarded source deltas. Their direct imports did not change. The previous driver, graph, ZF hash and 81-row ancestry are in `../ha87-zf-fallback-failure-and-rebase/` and subsequent source-drift evidence. New guarded author run `/tmp/ha87-focused-validator-rebase-8o6bp_pm` is live; its final result and independent replay remain pending.
