# Candidate-PRA proof of the fixed ZFC refutation witness bound

`PRAWitnessZFCRefutationBound.PRA_proves_refutation_bound` is an unconditional
Lean proof-existence theorem in the repository's candidate PRA: for the actual
Foundation ZFC refutation sentence `ρ`, candidate PRA proves
`ρ → ∃ w, bnd ρ w`. It does not prove either `ρ` or `¬ρ`, specify a uniform
primitive-recursive witness bound, or by itself establish an equation/Con(ZFC)
equivalence. The standard-PRA presentation comparison remains a separate
formalization question.

The theorem combines the independently replayed strict positive and negative
ZFC derivation-core witnesses, the actual Foundation proof predicate, and a
model-wise closed-existential argument followed by first-order completeness.
The parent providers have 230 shared project objects, all byte-identical;
their 139 Foundation and five ZFCinPA objects are also pairwise identical.

Guarded author `/tmp/pra-zfc-refutation-bound-ieoiwzi6` and independent
same-parent replay `/tmp/pra-zfc-refutation-bound-pa6mj8mc` passed all four
rebuilt modules with matching source/object/full-log hashes. The packet freezes
their sources and logs and guards 264 union project objects, 259 observed
workspace project sources, all 139 selected Foundation and five selected
ZFCinPA object bytes, and the compiler. The runs remove workspace project
Lake-object fallback. Both use the same already-replayed parent providers;
Foundation, ZFCinPA Instances and package transitive source/object ancestry
remain inherited. No independent full rebuild of that external boundary is
claimed.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-zfc-refutation-bound-strict-replay/replay.py`.
