# Positive-coordinate circuit identification

`SplitCircuitTranslation59.positiveValue_eq_naturalValue` proves the exact
identity between the pinned 473-operation positive and 480-operation natural
parent circuits:

```
positiveValue p x = naturalValue p (fun i => x i - 1).
```

It holds over every commutative ring for every twelve-leaf tuple `p`.
The certificate maps every retained register to its natural-circuit reference.
The nine input and two translation registers are checked directly. One tail
multiplication swaps its operands and is justified by commutativity; every
other retained node has exactly the same operation and mapped references.
Local node equations and evaluator uniqueness establish equality of the full
programs without expanding the output expression.

`SplitPositiveRecipe59.positiveValue_eq_recipe` identifies the positive parent
with `SplitNinePolynomial59.mixedValue`, using the eight raw coordinates and
internal `j = x7-1`. `jointPositiveValue_eq_recipe` gives the corresponding
identity for the 456-operation shared-power circuit. The two
`positivePolynomial_eq_recipe` theorems identify the actual `MvPolynomial`
data under the same twelve fixed-leaf binding as the natural recipe proof.

`exists_positive_zero_iff_natural_zero` proves the exact correspondence between
positive natural roots of the 456-operation circuit and unrestricted natural
roots of the 463-operation circuit. Both directions supply the coordinate
translation explicitly. Its fixed integer tuple remains arbitrary.

The dedicated checks audit the circuit translation, scalar identities,
polynomial identities and root equivalence. Only Lean's standard axioms occur.
The whole-port native calibration and the object-language ZFC biconditional
remain separate obligations.
