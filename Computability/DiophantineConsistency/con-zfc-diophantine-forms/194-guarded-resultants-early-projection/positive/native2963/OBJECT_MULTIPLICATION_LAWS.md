# Multiplication laws over internal omega

`ObjectMultiplicationLaws` proves left zero, left successor and commutativity
for the existing `MulRel` graph. Every natural input ranges over the entire
omega of an arbitrary `ZFAxioms` model. No input is assumed to be a quoted
external Lean natural number.

The left-successor law keeps the addition witness explicit:

```text
MulRel x y z  and  AddRel z y w  imply  MulRel (succ x) y w.
```

Its induction predicate is an actual finite formula relating multiplication
and addition graphs. The step uses the previously checked internal addition
commutativity, associativity and successor laws. A second supplied induction
formula proves multiplication commutativity. The zero law is a direct
definable induction using the right-successor equation. Auxiliary value
lemmas make zero and successor identities explicit for the existing
definable addition operation.

`multiplicationCommutativeForm` is a closed sentence for the actual graph,
and `zfc_proves_multiplication_commutative` is an actual
`BProv ZFCax_s [] multiplicationCommutativeForm` derivation. Completeness
is applied only after validity is proved in every model, including
nonstandard models. No consistency or model-existence assumption is used.
All ten public axiom audits use only the standard Lean axioms.

`ObjectDistributivity` further proves both distributive laws and
multiplication associativity with every intermediate value explicit.
Again the induction predicates are supplied object formulas; the proofs
cover every internal natural. The closed distributivity and associativity
sentences have actual ZFC derivations. Its eight public audits use only
the standard Lean axioms.

This is internal arithmetic infrastructure. Arithmetic coding and the full
internal consistency versus polynomial-unsolvability equivalence remain
further obligations.
