# Independent exact degree of the 84-row 2011 graph

The read-only [audit](audit.py) exited 0 in normal and optimized Python with
identical [receipts](CHECK.json), using explicit checks rather than assertions;
the [terminal observation](terminal-observation.json) records both exits. It
pins the full graph to commit `20c4dd9d3c`, checks all 84 rows, thirteen inputs
and four ports are live, and counts 49 multiplications, 18 additions and
17 subtractions.

The exact symbolic upper bound tracks the top three total-degree layers in
each graph node. It verifies the full main-norm cancellation to degree 18,
then checks that the degree-48 and degree-47 layers of `correctedU` cancel,
leaving degree 46. The output is therefore at most degree 92. Independently,
using all four **actual** fixed 2011 port values modulo 1,000,000,007 and
substituting t for all thirteen variables gives coefficient 557370225 for
`t^92`. This nonzero coefficient proves exact degree 92 after the fixed-port
specialization. Changing the correction sign restores degree 96 in the
diagonal calculation; dropping the corrected square reduces the tested degree
to at most 80.

All four full compressed port payloads and raw hashes are pinned and compared
with the previously captured Lean `#eval` values using its pinned receipt;
that is executable Lean plus external comparison, not an internal equality
theorem. Current 2011 port-definition sources are also hash-pinned. The
result is an external exact degree check for the graph, not yet a paired
Lean graph-to-expression binding, TeX/PDF interpretation, iPRA endpoint or
global-minimum proof. Foundation outer-wrapper and package-transitive/dynamic
ancestry qualifications remain.
