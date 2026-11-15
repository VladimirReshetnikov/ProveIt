import Std

/-!
# Elementary constructive distinctions between finiteness statements

This file is about arbitrary predicates on `Nat`.  It does not formalize
Faltings' theorem, machine undecidability, or an object-level iPRA derivation.
It checks the purely logical bridges used in the accompanying report.

The proofs use intuitionistic reasoning.  There are no additional axioms,
`sorry` placeholders, or uses of `Classical`.
-/

namespace FaltingsIPRA.Logic

/-- A cardinality upper bound of one, without a point or a complete list. -/
def AtMostOne (P : Nat → Prop) : Prop :=
  ∀ p q, P p → P q → p = q

/-- A positive numerical upper bound on every member's code. -/
def Bounded (P : Nat → Prop) : Prop :=
  ∃ B, ∀ p, P p → p ≤ B

/-- Agreement of two predicates throughout the inspected finite prefix. -/
def PrefixAgree (B : Nat) (P Q : Nat → Prop) : Prop :=
  ∀ p, p ≤ B → (P p ↔ Q p)

theorem bounded_of_unique_member {P : Nat → Prop}
    (unique : AtMostOne P) {k : Nat} (hk : P k) : Bounded P := by
  refine ⟨k, ?_⟩
  intro p hp
  exact Nat.le_of_eq (unique p k hp hk)

theorem bounded_of_no_member {P : Nat → Prop}
    (none : ¬ ∃ p, P p) : Bounded P := by
  refine ⟨0, ?_⟩
  intro p hp
  exact False.elim (none ⟨p, hp⟩)

/-- Even an abstract predicate with at most one member has a double-negated
bound.  This theorem supplies no positive bound and performs no case split
on the unbounded assertion that the predicate is inhabited. -/
theorem atMostOne_doubleNeg_bounded {P : Nat → Prop}
    (unique : AtMostOne P) : ¬¬ Bounded P := by
  intro noBound
  have none : ¬ ∃ p, P p := by
    intro inhabited
    obtain ⟨k, hk⟩ := inhabited
    exact noBound (bounded_of_unique_member unique hk)
  exact noBound (bounded_of_no_member none)

/-- The decidable empty predicate. -/
def EmptyPredicate (_ : Nat) : Prop := False

/-- A decidable singleton whose only member lies just beyond the prefix B. -/
def HiddenSingleton (B p : Nat) : Prop := p = Nat.succ B

instance : DecidablePred EmptyPredicate :=
  fun _ => isFalse (fun h => h)

instance (B : Nat) : DecidablePred (HiddenSingleton B) :=
  fun p => inferInstanceAs (Decidable (p = Nat.succ B))

theorem empty_atMostOne : AtMostOne EmptyPredicate := by
  intro p q hp _
  exact False.elim hp

theorem hidden_atMostOne (B : Nat) : AtMostOne (HiddenSingleton B) := by
  intro p q hp hq
  exact hp.trans hq.symm

theorem hidden_has_member (B : Nat) : ∃ p, HiddenSingleton B p :=
  ⟨Nat.succ B, rfl⟩

theorem empty_has_no_member : ¬ ∃ p, EmptyPredicate p := by
  intro inhabited
  obtain ⟨p, hp⟩ := inhabited
  exact hp

theorem hidden_absent_on_prefix (B : Nat) :
    ∀ p, p ≤ B → ¬ HiddenSingleton B p := by
  intro p hp hidden
  have impossible : Nat.succ B ≤ B := hidden ▸ hp
  exact Nat.not_succ_le_self B impossible

theorem empty_hidden_prefixAgree (B : Nat) :
    PrefixAgree B EmptyPredicate (HiddenSingleton B) := by
  intro p hp
  constructor
  · intro empty
    exact False.elim empty
  · intro hidden
    exact hidden_absent_on_prefix B p hp hidden

/-- At every finite cutoff there are two explicit decidable predicates,
both with cardinality at most one, agreeing up to the cutoff but having
different answers to the question whether any member exists. -/
theorem prefix_agreement_does_not_determine_emptiness (B : Nat) :
    PrefixAgree B EmptyPredicate (HiddenSingleton B) ∧
    AtMostOne EmptyPredicate ∧
    AtMostOne (HiddenSingleton B) ∧
    (¬ ∃ p, EmptyPredicate p) ∧
    (∃ p, HiddenSingleton B p) :=
  ⟨empty_hidden_prefixAgree B, empty_atMostOne, hidden_atMostOne B,
    empty_has_no_member, hidden_has_member B⟩

/-- Inspecting only the prefix through B cannot certify emptiness for
every predicate, even if each predicate is known to have at most one member.
The displayed counterexample is decidable. -/
theorem finite_prefix_not_universal_emptiness_certificate (B : Nat) :
    ¬ (∀ P : Nat → Prop, AtMostOne P →
      (∀ p, p ≤ B → ¬ P p) → ¬ ∃ p, P p) := by
  intro claimedCertificate
  have empty := claimedCertificate (HiddenSingleton B)
    (hidden_atMostOne B) (hidden_absent_on_prefix B)
  exact empty (hidden_has_member B)

#print axioms bounded_of_unique_member
#print axioms bounded_of_no_member
#print axioms atMostOne_doubleNeg_bounded
#print axioms prefix_agreement_does_not_determine_emptiness
#print axioms finite_prefix_not_universal_emptiness_certificate

end FaltingsIPRA.Logic
