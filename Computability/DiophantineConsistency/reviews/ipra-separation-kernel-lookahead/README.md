# Exploratory SeparationKernel compile

Tool session 37669 exited 0 and printed `PASS 0`. It compiled the captured
`SeparationKernel.lean` (SHA-256 `65707fe43e312da9349451f67ca625c7d7e7558367135b2bc0457a636b6a9683`)
using Lean `-M8000 -j1 -DElab.async=false`, a private source root, and a
`LEAN_PATH` consisting of the historical 258 peer followed by the package
mirror. `compile.log` is empty. `state.json` records the actual Lean exit,
source and binary hashes, the historical peer state and all three direct
import object hashes; those inputs matched before and after the compile.

The command was executed through a one-off Python heredoc and did not have a
separately pinned driver file. Its environment mixes the new source with
historical objects; package-transitive and object ancestry are inherited. This
is a lookahead elaboration check only, not an authenticated current-source
closure, independent replay, or proof of the final endpoint.
