# Later upstream K217 symbolic execution and dispatch refactors

This merge preserves `0d56613ba8` and `5115d60afe` after the phase15 K215
checkpoint. `EnumDom` replaces list-selection machinery with symbolic
command-execution equations and two local tactic macros. Its non-falsity
conditions and MP halt branches remain explicit. `L2RootDom` factors repeated
selector decrements and break/fall-through composition into four small helpers;
the dispatch statements and Clean/halting conditions remain unchanged. The
obsolete root-fork producer is retired by upstream.

The complete diffs were read as code. No compiler or supplied producer was run
for these K217 changes, and this merge does not claim new local K217 acceptance.
Both changed Lean modules lie outside the 199-project checked K215 union;
every source hash in that union remains exact. The machine and the phase15
proof evidence are unchanged. The [map](map.json) binds the four upstream paths,
including the producer deletion.
