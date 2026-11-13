# Independent 943-row local decoder audit

The read-only [audit](audit.py) of `a559988b8a` actually exited 0 in session
93216; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object/log and three seed chains, direct imports,
complete joined overlay inventories, recorded child and outer exits, and
successful reruns of the local-iff, table and tile-payload parent audits.
Both logs give the three expected theorem reports with Lean metatheory
`propext`, `Classical.choice`, and `Quot.sound`, without warnings or
`sorryAx`. No Lean compile was rerun.

For each external `Fin 943` table index, the first theorem derives a model
tile value strictly between 0 and `2^41`. Assuming each model selector
`f(i) ≤ 1`, the second derives `∑ f < 2^10`; with the additional explicit
assumption `W < 2^41`, the final theorem proves the aggregate no-carry
condition equivalent to the empty-cell case or exactly one selected row with
W equal to its tile value. The model operations and the precise aggregate
formula are displayed in the [source packet](../../research/ordinary12-ipra-bridge/compact44-943-decoder-prototype/README.md).

The table's comparison with the retained JSON remains external. The theorem
does not derive selector or W bounds from the graph, bind K or the full port
tuple, establish K215 simulation, calibrate the checker, or prove an iPRA
equivalence. `Fin 943` is an external fixed finite type. Inherited providers
lack a complete printed axiom inventory; Foundation outer-wrapper and
package-transitive/dynamic ancestry qualifications remain. Resource values
are samples. The later upstream additions in `6f8dd13085` postdate this
frozen provider chain.
