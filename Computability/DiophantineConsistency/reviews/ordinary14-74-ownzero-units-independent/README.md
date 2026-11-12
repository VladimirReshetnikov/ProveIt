# Independent source review: 74 own-zero guard unit

The composition feeds the same literal 74 valuation, own zero, beta cast,
positive beta and J/w/s assumptions to `factor_units_of_zero`; its three
additional residue hypotheses come from `restricted_residues` on that same
valuation. The output tuple is ordered first/main/aux/guard/strong, so
`h.2.2.2.1` selects the guard pair's positive unit, with no separate sign
assumption for the guard.

The `unit_iff_one` source statement and proof match the established generic
source proof in `Compact44.FreeJ13`: the split evaluation and embedding convert
pair equality `a=b+1` to difference-ring value one in the correct direction.
The review checker compares the actual source interfaces, checks 1,681 finite
pair conversions, reruns the independent three-residue review, and reproduces
the author receipt.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B reviews/ordinary14-74-ownzero-units-independent/check.py | cmp - reviews/ordinary14-74-ownzero-units-independent/observation.json`.
This is a source/interface review; imported drafts and tactics remain
unelaborated. It does not prove h>1, a 74↔75 model map, coherent providers,
the iPRA endpoint, or physical-byte/PDF binding. No Lean run was performed.
