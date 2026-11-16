# Lean outline: category interfaces and the object-theory bridge

This is a design document, not a claim that the displayed code has been compiled.
The packet separately provides uncompiled source-level proof expressions
whose conclusions use the actual embedded `Prf PRAAx` judgement.
The definitions below expose all data required for the category arguments.

## 1. Semantic definitions, with no hidden choice

Start from `import Mathlib.Data.List.Basic` and `import Mathlib.Data.Finset.Basic`
if using mathlib. The concrete guarded interface can equally be built from
Lean core's `List Nat` and `Bool` definitions.

```lean
structure Contract where
  witnessOK : Nat → Bool
  questionOK : Nat → Bool
  test : Nat → Nat → Bool

structure ContractHom (A B : Contract) where
  forward : Nat → Nat
  query : Nat → Nat → List Nat
  forward_typed : ∀ x, A.witnessOK x = true →
    B.witnessOK (forward x) = true
  query_typed : ∀ x v, A.witnessOK x = true →
    B.questionOK v = true →
    ∀ u ∈ query x v, A.questionOK u = true
  local_sound : ∀ x v, A.witnessOK x = true →
    B.questionOK v = true →
    (∀ u ∈ query x v, A.test x u = true) →
    B.test (forward x) v = true

-- Proof-relevant query lists are compared by membership, so reordering
-- and duplicate removal do not change an arrow.
def ContractHom.Equivalent {A B : Contract}
    (f g : ContractHom A B) : Prop :=
  (∀ x, A.witnessOK x = true → f.forward x = g.forward x) ∧
  (∀ x v, A.witnessOK x = true → B.questionOK v = true →
    ∀ u, u ∈ f.query x v ↔ u ∈ g.query x v)

def Realizes (A : Contract) : Prop :=
  ∃ x, A.witnessOK x = true ∧
    ∀ u, A.questionOK u = true → A.test x u = true
```

`identity` has forward map `id`, query `fun _ u => [u]`, and direct typing
and soundness proofs. Given `f : ContractHom A B`, `g : ContractHom B C`,
`compose g f` has:

```lean
forward := fun x => g.forward (f.forward x)
query := fun x w => (g.query (f.forward x) w).flatMap (f.query x)
```

For `query_typed`, unpack membership in the flatMap to a middle challenge
`v`, prove its validity using `g.query_typed`, then apply `f.query_typed`.
For `local_sound`, apply `g.local_sound`. Given `v` in its query list,
apply `f.local_sound`; turn every membership `u ∈ f.query x v` into
membership of the composite list using the same flatMap witness `v`.
This is the complete proof strategy and does not require any classical
instances. Identity and associativity are proved with `Equivalent`, using
membership in singleton and flatMap. Equivalence is reflexive, symmetric,
transitive, and congruent under composition by the same membership lemmas.

`realization_transport` takes the original realization witness `x` and
uses `f.forward x`. For an output challenge `v`, apply `f.local_sound`;
input challenge membership is valid by `f.query_typed`, so the original
realization hypothesis provides the required test equality.

These structures are semantic Lean definitions. Their function fields are
**not evidence of primitive recursiveness**. Add a second layer containing
PR syntax and proofs that the fixed functions used by a theorem are denoted
by that syntax. Do not quantify over every `Contract` value and infer that
its operations can be evaluated by iPRA.

## 2. Presented categories and Yoneda

The direct arithmetic interface has fields:

- `objOK : Nat → Bool`;
- `homOK : Nat → Nat → Nat → Bool`;
- `eqv : Nat → Nat → Nat → Nat → Prop` (or Bool in the decidable case);
- `ident : Nat → Nat`;
- `comp : Nat → Nat → Nat → Nat → Nat → Nat`, with arguments
  `(a,b,c,g,f)` for `g ∘ f`;
- guarded equivalence, typing, congruence, identity, and associativity laws.

A contravariant family over this presentation has:

- `mem : Nat → Nat → Bool` for `u ∈ F(x)`;
- `rel : Nat → Nat → Nat → Prop` for equality in `F(x)`;
- `act : Nat → Nat → Nat → Nat → Nat`, where `act x y f u` denotes
  `F(f)(u)` for `f : x → y`;
- guarded typing, relation congruence in arrows and elements, identity,
  and contravariant composition laws.

For fixed `A`, a representable transformation has an operation
`alpha : Nat → Nat → Nat`, where `alpha x f ∈ F(x)` for `f : x → A`;
it carries typing, arrow congruence, and naturality proofs.

The main semantic theorem's target is:

```lean
∀ x f, C.objOK x = true → C.homOK x A f = true →
  F.rel x (alpha x f)
    (F.act x A f (alpha A (C.ident A)))
```

Instantiate naturality at the pair `(f : x → A, ident A : A → A)`.
Its left member is `alpha x (ident A ∘ f)`. Use the category left identity
law and the arrow congruence field of `alpha` to replace it by `alpha x f`.
Transitivity of `F.rel` completes the proof. The inverse construction
`alpha_a x f := F.act x A f a` is natural by the contravariant action law;
evaluation at the identity is the action identity law.

For the finite version, implement all domains as explicit natural bounds
and all functions as canonical arrays. Then naturality is the PR Boolean
conjunction of its finitely many instances. A proof of the semantic theorem
can be specialized to these array operations, while the object-theory
translation follows the same fixed derivation with arithmetic guards.

## 3. Finite sets, limits and colimits

Definitions:

- `FinMap n m`: a length-`n` array of naturals all below `m`;
- canonical sequence/array coding into `Nat`;
- `FiniteCategory`: object bound, arrow bound, source/target tables,
  identity table, composition table, and PR Boolean validation;
- `FiniteDiagram`: finite category code plus cardinalities and arrow tables.

For `FinMap` laws use entrywise equality and the array-lookup equations.
The complete finite limit algorithm is:

1. enumerate mixed-radix tuples below `product cardinalities`;
2. keep precisely tuples satisfying every arrow equation;
3. define projections by lookup;
4. map a cone point to the rank of its coordinate tuple in the kept list;
5. prove the tuple was kept using its cone equations;
6. prove uniqueness by coordinate equality and injectivity of list ranking.

The complete finite colimit algorithm is:

1. form the tagged union of size `sum cardinalities`;
2. build the reflexive symmetric generator matrix;
3. compute bounded Warshall closure for exactly that sum many rounds;
4. take each class's least member by bounded search;
5. rank distinct minima;
6. descend any cocone by its value at the least member;
7. propagate equality along bounded paths to prove factorization;
8. prove uniqueness on each representative.

The nontrivial invariant for Warshall is bounded reachability by paths with
restricted intermediate vertices. Encode paths with an explicit length bound
and use a PR loop-deletion operation to justify shortening. Do not replace
this with an unbounded existential path invariant in quantifier-free induction.

Finite exponentials use base-`m` digits and the code bound `m^n`. Prove digit
reconstruction and the bound on the finite digit sum by Booleanized induction.
Handle `n = 0` and `m = 0` before the division lemmas. Then both exponential
laws are entrywise digit identities.

## 4. Object-theory implementation milestones

1. **Numerical layer.** Supply PR syntax and defining equations for tuple
   coding, finite-list membership, concatenation, finite union, table lookup,
   bounded conjunction, bounded selection, and powers. Reuse validated
   repository components where their exact interfaces match.
2. **Predicate layer.** Compile every bounded table-validation condition to
   an equality of a PR Boolean term to `1`. Prove both directions of each
   compilation equivalence in the embedded deduction system.
3. **Fixed categorical derivations.** Build embedded derivations for inverse
   uniqueness, split-monic cancellation, adjunction inverse maps, and the
   Yoneda component identity. These need intuitionistic implication,
   universal specialization/generalization, equality, and congruence only.
4. **Finite construction derivations.** For each loop state the exact Boolean
   invariant. Produce the corresponding quantifier-free induction instance,
   then construct the embedded proof of its correctness.
5. **Scope gate.** A theorem is labeled `object checked` only if its Lean
   conclusion is the repository's embedded derivability type (for example
   `Prf PRAAx ...`) or a checked constructor of such derivations. An ambient
   Lean theorem about `Nat`, `Fin`, `List`, or category structures is labeled
   `semantic checked`, even if its mathematical proof is intuitionistic.

No complete generic compiler is asserted by this document. These milestones
specify finite, inspectable obligations for completing one.
