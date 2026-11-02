# Symbolic graph saturation outputs

`CompactSymbolicGraphSaturation.graph_saturation` exposes both `NoCarry`
consequences of the existing graph saturation client after using the symbolic
low and high mask population, residue and bound results. Its graph zero,
positive variables, model port equalities and inequalities, beta, radix,
repunit and product assumptions remain explicit in the theorem. It is a
conditional model theorem: it does not bind the retained coefficients or
connect the results to a machine computation.

The existing symbolic graph-digit client used the first saturation result
internally and discarded the second. This client makes both available for a
future composition with the graph-derived radix and weighted-congruence results;
it does not yet perform that composition.

Exploratory Lean session 58239 exited 0 without warnings and printed
`[propext, Classical.choice, Quot.sound]` for the named theorem. It used the
author side of the independently audited fixed-graph provider, with inherited
provider and package qualifications. A paired replay and independent audit of
this new client remain open; see `observation.txt` for the exact command.
