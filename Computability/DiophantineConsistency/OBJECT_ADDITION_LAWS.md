# Addition laws for internal natural numbers

`ObjectAdditionLaws` proves left zero, left successor, commutativity and
associativity for the existing internal `AddRel` graph in every `ZFAxioms`
model. Its natural arguments range over the model's entire omega. The
results do not assume that these arguments are images of external Lean
natural numbers.

Each induction supplies an explicit `SetTheory.Form` to `omega_ind`.
The left-successor predicate relates two addition graphs via actual
successor formulas. The commutativity predicate reverses the two inputs
without changing the output. The associativity predicate keeps all
intermediate values explicit. Their satisfaction specifications connect
the formulas to the semantic graph predicates before induction is used.
Totality, uniqueness and the existing right-successor equation then prove
the zero and successor cases.

`addValue_comm` and `addValue_assoc` give the corresponding identities for
the existing definable addition value. They retain explicit membership
hypotheses in internal omega, so no algebraic laws are asserted for
arbitrary sets.

The module also supplies actual closed sentences and proofs:

```lean
zfc_proves_addition_commutative :
  BProv ZFCax_s [] additionCommutativeForm

zfc_proves_addition_associative :
  BProv ZFCax_s [] additionAssociativeForm
```

First-order completeness applies because the semantic arguments cover
every model of sealed ZFC, including nonstandard models. No model-existence
or consistency assumption is used. The dedicated audit covers twelve
public endpoints and uses only the standard Lean axioms.

These laws are prerequisites for internal arithmetic compiler correctness.
They do not yet give an internal equivalence between the consistency
sentence and polynomial unsolvability, nor a transfer principle for
arbitrary external Lean arithmetic theorems.
