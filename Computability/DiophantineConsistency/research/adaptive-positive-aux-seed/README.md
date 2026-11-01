# Oriented auxiliary seed from a machine run

The auxiliary seed in `ArithmeticConstructionAssembly` carries an orientation
`L=|L-M|+M`, where `L=f² c T` and `M=f² R+c`. The carrier's auxiliary norm
and positive multiplier imply `|L-M|>0`, so this particular constructed
seed has `M<L`. The proof does not assert that every zero has this sign.

`ArithmeticAdaptiveOrientedWitness2011` preserves the sign alongside the
explicit thirteen-coordinate adaptive witness. Its conditional theorem retains
all enriched assembly hypotheses. Its run theorem applies the unbounded
construction and the proved local-normalization lemma: an internal machine
halting time yields a positive adaptive zero and an old seed with strict
orientation. Mapping this witness through the 42-, 43- or 32-variable graph
is a separate obligation, and no native iPRA endpoint for that mapping is
claimed here.

The [paired replay](../../reviews/adaptive-positive-aux-seed-replay/README.md)
rebuilds the three modules on a fixed provider; transitive and dynamic
ancestry remains inherited.
