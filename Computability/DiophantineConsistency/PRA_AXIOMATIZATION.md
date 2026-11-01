# The classical PRA presentation used as an intermediate

The active target is now existence of a proof in **intuitionistic PRA**; see
[IPRA_PROVABILITY_PLAN.md](IPRA_PROVABILITY_PLAN.md). The intuitionistic theory
has a candidate native definition. Its literal 14-variable equation endpoint
has passed matching fixed-snapshot replays on a repaired project-origin
provider. A current-source replay and a broader standard-presentation
comparison remain open; the original 848-module ancestor is author-only and
external package-transitive and dynamic ancestry remains inherited.
The existing `PRATheory.PRA`, defined in
[`PRATheory.lean`](Lean/DiophantineConsistency/PRATheory.lean), is a classical
first-order theory with equality, an expanded language of primitive-recursive
functions, and induction for quantifier-free formulas. It is an intermediate
whose proof objects cannot be presented as intuitionistic PRA proofs without
an additional verified translation.

## Language

For each finite arity, function symbols are finite construction codes. The
constructors are zero, successor, projection, composition, and primitive
recursion; distinct codes are distinct symbols even if they compute the same
function on the natural numbers. The relations are equality and strict order.
The definitions are in [`PRAFiniteFunctionCodes.lean`](Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean)
and [`PRALanguage.lean`](Lean/DiophantineConsistency/PRALanguage.lean). Lean
proves that every such code computes a primitive-recursive function on ℕ and
every primitive-recursive ℕ-valued function of finite arity has a code.
Addition, multiplication and one are particular codes, not extra independent
function symbols.

## Axioms

All free variables in the displayed equations are universally closed. In
addition to first-order equality axioms, the theory has:

* For each arity, the zero code equals the nullary zero code; projection codes
  return the corresponding argument. For a composition code, the function is
  equal to its defining composition.
* For each recursion code `h = prec(f,g)`, the equations
  `h(0, x̄) = f(x̄)` and `h(S(n), x̄) = g(n, h(n,x̄), x̄)`.
* `S(x) ≠ 0` and `S(x) = S(y) → x = y`.
* `x < y ↔ ltBit(x,y) = 1`, where `ltBit` is the constructed
  primitive-recursive code computing the nonzero test for `y − x`, with
  truncated subtraction.
* For every quantifier-free formula `φ(n, x̄)` in the **full expanded
  language**, the universal closure of
  `φ(0,x̄) → (∀ n, φ(n,x̄) → φ(n + 1,x̄)) → ∀ n, φ(n,x̄)`.
  Parameters `x̄` are allowed. Quantifier-free here means no quantifiers in
  `φ`; bounded quantifiers written out as quantifiers are not themselves
  quantifier-free. Here `n + 1` uses the designated addition and one codes;
  it is not syntactically the same term as the separately coded `S(n)`.
  Relating the two requires a derivation from the defining equations.

The union is exactly `core ∪ BasicAxiom` in `PRATheory.PRA`. In particular,
full first-order induction and Σ₁ induction are not added as axioms. The
proof system is classical; Lean's own metatheoretic principles used to prove
the existence of a derivation are not additional PRA axioms.

Schematically, `PRA ⊢ ψ` is a Lean proposition asserting the existence of a
derivation of the object-language sentence `ψ` from precisely these axioms in
Foundation's classical first-order proof system. The arithmetic sentence is
mapped into this language by `PRALanguage.embedding`; the mapping does not add
axioms. A Lean proof of this proposition is metatheoretic evidence for an
object-theory derivation, not a proof of `ψ` from Lean's axioms presented as if
it were a PRA derivation.

## Scope of the comparison

This is a natural candidate presentation of first-order PRA. The repository
proves that the usual natural numbers satisfy its axioms, and proves many
concrete translations and arithmetic consequences. A separate Lean theorem
identifying this presentation with every standard presentation of PRA, or a
general IΣ₁-to-PRA conservation theorem, is not currently claimed. See
[PRA_PROVABILITY_PLAN.md](PRA_PROVABILITY_PLAN.md) for the exact proof target,
the status of the specific ZFC witness bound, and the remaining equation and
dependency verification.
The intended result is an intuitionistic PRA derivation of the equivalence
between no positive solution and the chosen formal `Con(ZFC)` sentence, not a
proof of either side on its own.
