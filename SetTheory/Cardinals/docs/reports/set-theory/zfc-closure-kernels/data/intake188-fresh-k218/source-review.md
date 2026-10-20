# K218 direct-leaf execution review

Reviewer: opening_encoder. The submitted archive is recovered from arrival
`c4568161bf0eafeabc9e6f5a4a5c8c0a90c22f70`; ZIP SHA-256 is
`f22c853e1da435a932f9bf69321cfd790f7318acc2cc340a27f275d1c0d43f2c`.
Its 99 files were safely extracted to a pristine directory. Execution uses a
separate copy; original delivery bytes are unchanged.

The reviewer read all nine Python files used directly or imported by the six
selected jobs: `common.py`, `source_language.py`, `check_source218.py`,
`build218.py`, `check_classical218.py`, `canonicalize218.py`,
`check_blank_startup.py`, `check_runtime218.py`, and `audit_runtime218.py`.
The runtime additionally imports the exact pinned K221 `build221.py`,
`source_language.py`, `symbolic_runtime.py`, and `independent_runtime.py`, and
reads its pinned legacy mapping. These inherited implementations were read in
full; the current exact pins are in `plan.json`. Imports are standard library
plus these files. No network operation, shell invocation, or code evaluation
occurs in the selected leaf closure. Output writes are restricted by the
reviewed concrete arguments to fresh scratch output directories.

The original `reproduce.py` was read to identify its leaf order but was not
executed. Its manifest check and predecessor wrapper invocation are deliberately
outside this fresh run. The K219 archive is extracted as baseline data, while
only the five necessary K221 dependency files are recovered from the nested
K220/K221 archives. Their archive and individual-file identities are checked;
no ancestor suite runs. This is exact input binding, not a replay of a delivered
manifest/checksum suite. No Lean, Rocq or Coq code is invoked.

## Source and engine implications

The supplied source transformation retains all 4,744 primitive operations and
the exact ordinal control-flow graph of pinned K219. Five occurrences of a
closed, halt-free 26/19/7-leaf triple are reassociated. The final tree has
205 distinct DAG nodes, depth 38 and maximum zero run six. The independent
checker reconstructs the graph with explicit semantic continuations, distinct
from the source builder's two address-based resolvers.

The new state saving uses the immediate predecessor bit as a two-way context
marker. In the unfolded 219-state table, only 155/0 enters 85 and writes zero;
only 177/1 enters 212 and writes one. Merging 212 into 85 and changing 85/1 to
`1 L 190` reaches the respective original successor in three or five steps.
Read-zero behavior is identical and takes one step. The independent checker
examines all four marker/read combinations, preserves both cells, and never
touches the unknown exterior. Since start state 0 is not one of the merged
states, every later entry has its marker established by the unique incoming
edge. This supports the stated all-tape stuttering argument for this local
fold. The separate full runtime establishes the exact source interface of the
final table, including arithmetic paths that a decoder graph alone would miss.

This is a new successful decoder-context reuse; it does not rely on deleting
helper 302, on the previously failing CD8-positive endpoints, or on adopting
an unproved K/S-only formalism. The final source graph is exactly the accepted
K219 graph. There is no newly constructed 217-state machine in this review.

## Actual-run boundary

The reviewer-owned serial runner records one 180-second process cap for the
full runtime job and 60 seconds for each other leaf, with assertions enabled,
bytecode generation disabled and inherited Python path/optimization settings
cleared. Each process has its own process group; timeout kills that group and
retains stdout/stderr and partial outputs. Exact selected input hashes are
checked before and after execution. Raw result records remain unedited.

The full symbolic runtime's loops bound certificate construction, not register
values. Its cases range over arbitrary natural register values, blank gap,
first spare and remaining finite spare list. The independent audit checks
ordered guard coverage, all literal transition rows, affine clock positivity,
and independently derives the four unbounded one-block rules. These are
executable mathematical certificates, not a fresh proof-assistant endpoint.
The separately reviewed inherited calibration remains an inherited premise of
the final nonhalting/consistency composition and is not replayed here.

The status and exact measured counts are recorded only in the terminal actual
`result.json` and `review.json`. Portable adapters change only scratch path
selection. Their preparation is exercised once in a second fresh directory;
the portable runtime is not redundantly rerun.
