/-!
# `axiom`, and the axiom you did not realise you were assuming

Category (see `../../README.md`): **escape hatch**. Adding an axiom is the
sanctioned way to extend the logic, and `#print axioms` names it.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

/-! ## 1. The direct form -/

axiom bald : False

/-- info: 'bald' depends on axioms: [bald] -/
#guard_msgs in #print axioms bald

theorem anything (P : Prop) : P := bald.elim

/-- info: 'anything' depends on axioms: [bald] -/
#guard_msgs in #print axioms anything

/-! ## 2. The innocuous-looking form

An axiom does not have to *say* `False` to be `False`. This one reads like a
harmless universe-lowering convenience. -/

universe u
axiom lower : ∀ α : Sort u, α

theorem from_lower : False := lower False

/-- info: 'from_lower' depends on axioms: [lower] -/
#guard_msgs in #print axioms from_lower

/-! ## 3. Universe-collapsing axioms are *refutable*, not merely inconsistent

This is a genuine asymmetry with Rocq, which offers `Unset Universe Checking` as
a flag. Lean has no such flag — and it does not need one to *discuss* the
hypothesis, because the hypothesis is expressible and refutable inside Lean.
See `../../Paradoxes/Lean/TypeTheoryParadoxes/Girard.lean`, whose
`no_internal_universe` says exactly that no `V : Type u` decodes `Type u` with a
section, and reports no axioms at all. -/

/-! ## 4. The realistic failure: an axiom-free theorem that means the wrong thing

By far the most common way a working Lean user derives `False` is not any of the
above. It is a correct proof of a statement that does not say what its author
read it as saying. Nothing is assumed, `#print axioms` is clean, and the `False`
is real.

With `autoImplicit` on — the default outside Mathlib — an unbound identifier in
a statement silently becomes a universally quantified variable. So `ℕ` below is
*not* the natural numbers; it is a bound type variable, and the theorem asserts
something about *every* type, including `False`. -/

section
set_option autoImplicit true

/-- Reads as "there are two distinct naturals". Actually says: for every type
`ℕ`, there are two distinct elements of it. -/
axiom two_distinct : ∃ a b : ℕ, a ≠ b

theorem misread : False :=
  match two_distinct (ℕ := False) with
  | ⟨f, _, _⟩ => f

/-- info: 'misread' depends on axioms: [two_distinct] -/
#guard_msgs in #print axioms misread

end

/-! Here the audit *did* fire, because the statement was an `axiom`. Replace
`axiom two_distinct` with a genuine proof of the same over-general statement —
which is impossible here, but is entirely possible for a statement whose
over-generality is subtler, such as a missing side condition or an instance
argument that quantifies over all structures on a fixed type — and
`#print axioms` reports nothing while `False` still follows.

That is the class this repository's ground rules cannot fully defend against,
and it is why the rule is "state the toolchain, give a control, and read the
statement", not merely "run `#print axioms`". The Rocq counterpart, where the
statement is a lie for lexical rather than elaboration reasons, is
`../Coq/Spoofing.v`; the Lean lexical study is
`../../Audits/Lean/StringIdentity/`. -/
