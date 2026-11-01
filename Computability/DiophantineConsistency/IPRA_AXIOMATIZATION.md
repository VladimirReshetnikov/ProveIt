# The intuitionistic PRA candidate used in the proof

The final target is a derivation in the explicitly defined candidate
`IPRANativeTheory.nativeTheory`, not merely a derivation in classical PRA or
in Heyting arithmetic. Its exact definition is in
[`IPRANativeTheory.lean`](Lean/DiophantineConsistency/IPRANativeTheory.lean),
with its induction syntax in
[`IPRANativeInduction.lean`](Lean/DiophantineConsistency/IPRANativeInduction.lean).
This document describes those definitions; it does not assert that the final
equation equivalence has been proved.

## Logic and language

The object proof system is Foundation's intuitionistic first-order Hilbert
calculus `Int¹`. Its language has equality and strict order as relation symbols.
For every finite construction code there is a function symbol. Codes are built
from zero functions of each arity, successor, projections, composition, and
primitive recursion. Two different codes give different symbols even when
they denote the same function on the natural numbers. The code construction is
defined in [`PRAFiniteFunctionCodes.lean`](Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean).
Addition, multiplication and one are designated codes, not separate primitive
axioms. Variables range over the arithmetic domain.

## Nonlogical axiom schemes

All displayed free variables are universally closed; parameters in the schemes
are arbitrary finite lists.

1. Equality: `x = x`, and the full Leibniz substitution scheme
   `x = y → (φ(x, p̄) → φ(y, p̄))` for **every intuitionistic formula** `φ`,
   including formulas with quantifiers. This yields equality congruence for
   functions and relations.
2. Function definitions: every zero code returns zero; every projection code
   returns its selected argument; each composition code equals its defining
   composition. For each primitive-recursion code `h = prec(f,g)`, include
   `h(0, p̄) = f(p̄)` and
   `h(S(n), p̄) = g(n, h(n,p̄), p̄)`.
3. Successor and order: `S(x) ≠ 0`, `S(x) = S(y) → x = y`, and
   `x < y ↔ ltBit(x,y) = 1`, with `ltBit` the particular constructed PR
   code that tests whether truncated `y − x` is nonzero.
4. Induction: for each quantifier-free intuitionistic formula `φ(n,p̄)` in the
   full code language, include

   `∀ p̄ [φ(0,p̄) → (∀ n (φ(n,p̄) → φ(n + 1,p̄))) → ∀ n φ(n,p̄)]`.

   A quantifier-free formula is built from falsity and relation atoms using
   conjunction, disjunction and implication. Negation is implication to
   falsity. Bounded quantifiers written as quantifiers are not quantifier-free.
   The step `n + 1` uses the designated addition and one codes: it is not
   syntactically identical to `S(n)`, although their equality is an intended
   arithmetic consequence of the function equations.

There is no unrestricted induction scheme, general excluded middle, or Markov
principle among these axioms. In particular, classical negation-normal
`¬A ∨ B` cannot simply be substituted for the intuitionistic implication
`A → B` in the induction scheme.

## What has and has not been established

The classical intermediate `PRATheory.PRA` is described in
[`PRA_AXIOMATIZATION.md`](PRA_AXIOMATIZATION.md). A Lean theorem
[`IPRAFullGGTransfer.from_classical`](Lean/DiophantineConsistency/IPRAFullGGTransfer.lean)
transfers each derivation in that particular classical presentation to a
native-candidate derivation of its Gödel–Gentzen translation. It does not by
itself identify the translated consistency sentence with the intended native
consistency sentence. The exact equation equivalence and a Lean-checked
comparison with an independently specified standard presentation of
intuitionistic PRA remain open; see
[`IPRA_PROVABILITY_PLAN.md`](IPRA_PROVABILITY_PLAN.md).

A Lean theorem asserting `nativeTheory ⊢ ψ` is a metatheoretic assertion that
an object-theory derivation exists. Principles used by Lean in that
metatheoretic proof do not become additional object-theory axioms.
