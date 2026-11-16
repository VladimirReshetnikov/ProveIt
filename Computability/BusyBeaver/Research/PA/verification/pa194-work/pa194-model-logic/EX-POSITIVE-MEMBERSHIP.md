# Existential introduction for positive membership atoms

`simRuleExs_positiveMembershipAtom` proves the exact existential compiler
implication for every well-scoped positive binary source membership atom and
every legal source term, from the source sequent premises and
`RankedAdmission`. It holds in arbitrary candidate-PRA models whose arithmetic
reduct satisfies IΣ₁, including for nonstandard source syntax. The function-free
source terms are free-variable codes. The atom arguments under one binder are
either free variables or the binder's `#0`; the proof covers neither, either, or
both arguments containing that binder. Source membership arguments appear in
reversed numerical order.

The theorem does not cover negative membership or source equality atoms,
compound or quantified bodies, or yield a complete compiler or consistency
direction. `check-ex-positive-membership.sh` replays the source closure and
checks sixteen axiom reports. Any retained objects and workspace foundations
require their own provenance.
