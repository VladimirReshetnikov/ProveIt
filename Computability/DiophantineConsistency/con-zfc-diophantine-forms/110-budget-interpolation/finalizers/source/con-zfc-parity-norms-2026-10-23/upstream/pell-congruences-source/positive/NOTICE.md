# Attribution and scope

This component adapts the literal arithmetic-circuit builders and exact
polynomial-audit routines in Vladimir Reshetnikov's ProveIt repository,
at commit `cf4a5218a5a4e4358d3f5314151b6b05d4aa384e`:

* `Computability/DiophantineConsistency/con-zfc-diophantine-forms/70-residue-orientation/eleven/`
* `Computability/DiophantineConsistency/con-zfc-diophantine-forms/69-cones-pell/positive/`
* `Computability/DiophantineConsistency/con-zfc-diophantine-forms/74-centered-pell-gaps/`

The retained LICENSE is the source MIT license. The normalized Pell source,
fixed coefficient tuple, native compiler, and K215 syntactic calibration
remain inherited dependencies. The exact changes are described in PROOF.md
and positive_reductions.tex. Neither the earlier packages' formal status nor
their original verification receipts are transferred to the new equations.

This iteration combines rational-coordinate saturation with root transport,
separates the transport multiplier from the radical majorant, and uses the
cofactor argument for the smaller adaptive modulus. These are claims of
new combinations relative to the pinned repository, not literature-wide
priority claims for the individual ingredients.
