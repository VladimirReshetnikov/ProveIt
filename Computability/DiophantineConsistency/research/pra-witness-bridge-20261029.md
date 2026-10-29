# Candidate PRA: order witnesses and the induction-rule boundary

This note describes Lean declarations in the candidate first-order PRA language.
It does not claim that the candidate has been identified with a standard PRA
presentation, or that IΣ₁ is conservative over it.

## Fixed function symbols and order

The arity-indexed finite `Code` language has a symbol for every finite
primitive-recursive construction. `PRAFiniteFunctionCodes.eval_primrec` proves
that each **fixed** code evaluates to a primitive-recursive function, and
`exists_code_of_primrec` proves the converse existence statement. These results
do not supply a jointly primitive-recursive evaluator for arbitrary codes.

`PRAQOrder.PRA_proves_all_Q` proves that every actual Foundation Robinson Q axiom
has a candidate-PRA derivation after the ordered-ring language embedding.
The previously missing order axiom uses the candidate's strict-order definition
and two object-theory facts proved by open induction: subtraction cancels a
summand, and `y − x = 0 ∨ x + (y − x) = y`. These proofs work in every
candidate-PRA equality model, including nonstandard models. Foundation
completeness supplies the closed derivations.

`PRAQProofTranslation.PRA_proves_qTheorem` extends this to **every Q theorem**:
if Foundation's Robinson Q proves a sentence, candidate PRA proves its mapped
sentence. This existence proof uses first-order soundness and completeness;
it is not a verified executable proof-code transformer or an instance of
Foundation's separate `DirectInterpretation` structure.

`PRAQOrderWitnessCode` goes further for this particular order axiom. It gives an
explicit arity-two primitive-recursive code for `pred(y − x)`, proves its
standard evaluation and fixed-code primitive recursiveness, and proves in the
candidate object theory

```
∀ x y, x < y → x + succ(witnessCode(x,y)) = y.
```

The identity between the function symbol and the nested predecessor/subtraction
term is established in arbitrary candidate-PRA models from the actual defining
equations. This is a concrete, theory-certified witness for strict order. It
is not a general witness extraction theorem for Σ₁ formulas or a witness for
the Diophantine consistency equivalence.

## Link to the Parsons-rule development

`PRAInductionRule.open_induction_rule` proves admissibility of the induction rule
for each open candidate-language formula, from proofs of the universal
closures of its base and successor-step formulas. Free parameters are retained
and closed universally. `PRAParsonsOpenRule.parsons_open_induction_rule` states
this result using the actual `ParsonsRule.base` and `ParsonsRule.step` definitions.
The latter rule has a broader Σ₁ induction constructor; this adapter only
covers open matrices. In particular, there is no present theorem replacing an
arbitrary use of that Σ₁ rule with a candidate-PRA derivation.

To connect the present candidate to the Parsons witnessing route, the remaining
arithmetic work includes expressing its witnesses as fixed `Code`s, proving the
relevant defining equations and correctness **inside** the candidate theory,
and establishing the reduction for the full parameterized Σ₁ induction
rule. A language embedding or standard-model evaluation theorem alone cannot
provide this reduction. The candidate's induction axioms are not themselves
universal sentences, so applying a universal-theory Herbrand theorem also
requires a separately proved presentation/translation. Nothing in these
checkpoints supplies either that translation or Π₂ conservation.

The source and compiler-provider details for individual checkpoints are
recorded in the associated review evidence. They inherit the existing
Foundation cache; a fresh transitive Foundation rebuild is not claimed.

## Uniform term-to-code compilation

The [term compilation theorem](../reviews/pra-term-compilation-root.md)
compiles an arbitrary candidate-language term with n bound inputs to a
single finite `Code n` and gives an actual candidate-PRA derivation of the
universally closed equality to the original term. Its semantics are proved
in arbitrary equality models, and each resulting fixed code is primitive
recursive. Formula normalization and Σ₁ witnessing remain open.
