# PRA proof-existence target

The active objective requires a Lean proof that the equivalence between each
selected small equation's unsolvability and `Con(ZFC)` is provable in
primitive recursive arithmetic (PRA). The earlier request for an HA derivation
also remains relevant. Existence of an object-theory proof is enough; a
printed proof is not required.

## What is already proved

For the maintained 14-positive-variable equation,
[`HACurrentEquation2011.isigma1_proves_current_iff_consistency`](Lean/DiophantineConsistency/HACurrentEquation2011.lean)
is a closed Lean theorem producing a Foundation IΣ₁ proof of the equivalence
between the literal shifted no-zero sentence and Foundation's ZFC consistency
sentence. In the same module, `ha_current_iff_consistency` is a closed Lean
theorem producing the corresponding derivation in the repository's HA
calculus. The proof passes through the polynomial, machine and source bridges
in arbitrary internal models. These statements do not assert consistency of
ZFC itself.

The repository also records the mathematical consequence of Parsons'
Π₂-conservation theorem: IΣ₁ is Π₂-conservative over PRA. See, for example,
[Joosten, *Two Proofs of Parsons' Theorem*](https://www.phil.uu.nl/ozsl/articles/joosten01.pdf).
This is presently an **external mathematical argument**, not a Lean theorem
producing a PRA derivation. In particular, the `isigma1_proves...` Lean theorem
has an IΣ₁ conclusion; its docstring's PRA claim is not an additional Lean
conclusion. A repository and pinned Foundation source search found no PRA
calculus or formalized Parsons theorem. Thus the requested Lean PRA endpoint
remains open, even for the maintained equation. The previous HA progress
estimate predates the closed HA endpoint and does not estimate the PRA work.

The [source audit](research/pra-conservation-source-audit-20261029.md)
identifies Foundation's existing cut-elimination theorem and explains the
remaining arithmetic reduction and witnessing work. It also examines a direct
primitive-recursive witness route; neither route is already formalized.

A [first-order PRA design](research/pra-first-order-language-design-20261029.md)
specifies arity-indexed primitive-recursive codes, defining equations, full
language equality, parameterized quantifier-free induction and the exact
ordered-ring embedding. It is a design, not yet a Lean implementation.

The first [primitive-recursive function code module](Lean/DiophantineConsistency/PRAFunctionCodes.lean)
now represents fixed-arity codes and proves their exact correspondence with
Mathlib's primitive-recursive vector functions. Its [independent replay](reviews/pra-function-codes-root.md)
passed. The [finite syntax](Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean)
has decidable equality and a surjective semantics-preserving conversion; its
[independent replay](reviews/pra-finite-function-codes-root.md) also passed.
A [numeric codec](Lean/DiophantineConsistency/PRACodeEncoding.lean) now
has a proved arity-checked roundtrip and an [independent replay](reviews/pra-code-encoding-root.md).
The [first-order language](Lean/DiophantineConsistency/PRALanguage.lean)
now embeds the existing ordered-ring language and has a checked natural-model
reduct; its [independent replay](reviews/pra-language-root.md) passed.
The [candidate PRA theory](Lean/DiophantineConsistency/PRATheory.lean)
now defines its full axiom families and proves standard-natural-model validity;
its [independent replay](reviews/pra-theory-root.md) passed. A closed [object-theoretic add-one theorem](reviews/pra-add-one-root.md)
now connects the designated addition and successor symbols in that theory.
Compatibility with a standard PRA presentation, further arithmetic bridges,
primitive-recursive axiom recognition and conservation remain open. This is not a uniform primitive-recursive evaluator.

The [adaptive 13-variable expression binding](reviews/adaptive-expression2011-root.md)
now identifies the exact accepted polynomial and proves its single positive
shift over arbitrary commutative semirings. The [internal factor-magnitude theorem](reviews/adaptive-factor-magnitude2011-root.md)
now derives magnitude one for the four actual factors from the literal zero.
The [factor-unit theorem](reviews/adaptive-factor-units2011-root.md) now
excludes the negative units by internal modulo-four reasoning and derives all
four positive units. Pell recovery and zero-existence equivalence remain open.

The [exact hierarchy certificate](reviews/arithmetic-current-hierarchy2011-root.md)
now proves in Lean that both maintained source sentences are Π₁ and their
literal biconditional is Π₂. Its source-current replay was performed at the
recorded prior snapshot; subsequent upstream commits changed some prerequisite
sources. The certificate supplies a conservation input, not conservation or
PRA derivability itself.

## Concrete bridge to formalize

1. Choose and define a precise PRA language and proof calculus, including its
   primitive-recursive function symbols, defining equations and induction
   scheme. State the desired Lean conclusion using its actual derivability
   predicate. Bind the arithmetic language of the existing IΣ₁ proof to that
   PRA language, including the same Gödel coding and ZFC theory.
2. Prove in Lean that the exact equivalence is in the Π₂ fragment accepted by
   the conservation theorem, or produce a provably equivalent Π₂ normal form
   and a PRA derivation transporting the result back. Foundation's
   `Theory.consistent` is constructed as a Π₁ sentence; the current no-zero
   sentence is a universal closure of a negative equality. Their biconditional
   is a Boolean combination of Π₁ sentences, so the exact syntactic or
   normal-form bridge must account for both directions, coding of the fourteen
   variables, and the conservation theorem's precise language and hierarchy.
3. Formalize an applicable proof of Π₂ conservation, or a verified proof
   transformation with an equivalent precise contract. A prose reference,
   a new axiom, a standard-model truth argument, or an unproved transfer
   premise does not establish the requested endpoint. The conservation proof
   is substantial and cannot be inferred merely from the existing Lean
   completeness argument.
4. Apply the formalized transfer to the closed IΣ₁ theorem and export a
   closed Lean theorem asserting existence of a PRA proof of the exact stated
   equivalence. Check the actual theorem's axioms and the entire dependency
   chain. Establish corresponding internal transformations and endpoints for
   the other selected size-metric equations; external equivalence of their
   standard natural-number zero sets alone does not supply a PRA proof.

A possible classical normal-form calculation illustrates step 2. If
`A = ∀ a, P(a)` and `B = ∀ b, Q(b)`, then `A → B` is classically equivalent
over nonempty natural-number domains to `∀ b, ∃ a, (P(a) → Q(b))`, and the
other direction is analogous. Combining and coding the variables gives a Π₂
form when the matrices are suitably bounded or primitive recursive. This is
a route to investigate, not a Lean proof of the required equivalence or of
the conservativity theorem.

The task also continues to seek smaller rigorously certified equations;
size improvements and the proof-existence results for each proposed form must
be tracked separately.
