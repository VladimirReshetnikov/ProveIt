# Independent ordered 943-row table audit

The read-only [artifact audit](audit.py) of `8c9e4816b7` actually exited 0 in
session 20903; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record matched source/object/log chains, direct imports, recorded child and
outer exits, and a successful rerun of the window-parent audit. Both reports
give `[propext, Quot.sound]` for `row_bounds` and no axioms for `rows_length`
or `row_widths`, without warnings or `sorryAx`. No Lean compile was rerun.

The separate [checker controls](checker_controls.py) independently parse the
actual Lean list body and compare all 943 rows in order to the pinned JSON,
check their 8/9/8/9-bit bounds and ensure the markers enclose the actual
`rows` definition. The [result](checker-controls.json) records success and
rejection of optimized mode, reordered rows, a missing comma, a changed first
row and a duplicate marker. This is an external source/data comparison; it
is not a Lean theorem interpreting JSON.

The finite Lean list and width theorems do not bind the rows to K or the
other compact44 ports, prove their correspondence to K215 actions, simulate
the machine, calibrate the checker, or establish an iPRA proof. `Fin 943` is
an external finite index and should not be treated as an arbitrary internal
nonstandard range. Inherited window providers lack complete printed axiom
inventories; Foundation outer-wrapper and package-transitive/dynamic ancestry
qualifications remain. RSS values are samples. Merge `f6ad1e00b1` added
three thirteen-variable sources that were not inputs to this pair.
