# Pre-merge input snapshot for native 86/87 endpoint

This is a source-only input snapshot, not a Lean replay. It records 1,103 reachable project source hashes, 348 affected modules and source snapshots, all 943 parent project-object hashes, and the 568 present direct external object/companion files with resolved paths. The exact target is `IPRAAdaptiveNativeZFCChecks`. The manifest and driver were generated before the incoming `IPRABoundedErasure.lean` source change, so this snapshot is historical after that merge and is not the source-current build packet.

The parent is the independently checked post-merge induction peer, whose 848-module ancestor is author-only; Foundation/package transitive ancestry remains inherited. Any replay from this packet would require the workspace to match these frozen source hashes or a separately implemented frozen-source driver.
