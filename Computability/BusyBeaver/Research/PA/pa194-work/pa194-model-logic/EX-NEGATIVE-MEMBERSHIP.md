# Existential introduction for negative membership atoms

`simRuleExs_negativeMembershipAtom` proves the exact existential compiler
implication for every well-scoped negative binary source membership atom and
every legal source term, from the source sequent premises and `RankedAdmission`.
It holds in arbitrary candidate-PRA models whose arithmetic reduct satisfies
IΣ₁, including for nonstandard source syntax. The proof combines the positive
case's source-term classification with target specialization, covering neither,
either, or both atom arguments containing the substituted binder. Numerical
target membership arguments occur in the reverse source order.

The theorem does not cover source equality atoms, compound or quantified
bodies, or yield a complete compiler or consistency direction.
`check-ex-negative-membership.sh` replays its source closure and checks ten
axiom reports. Any retained objects and workspace foundations require their
own provenance.
