import Init

/-!
Kernel-checkable core of a proposed signed-congruence interface.
This file deliberately has no Mathlib dependency.  The integer instance uses
equality of remainders, the same relation as Mathlib's Int.ModEq.  Replacing
the project proof with this API is a separate integration step.
-/

namespace ProofSimplification.SignOrbit

universe u

structure Congruence (α : Type u) where
  rel : α → α → Prop
  refl : ∀ a, rel a a
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  neg : α → α
  neg_neg : ∀ a, neg (neg a) = a
  neg_rel : ∀ {a b}, rel a b → rel (neg a) (neg b)

namespace Congruence

variable {α : Type u} (C : Congruence α)

def Signed (a b : α) : Prop := C.rel a b ∨ C.rel a (C.neg b)

theorem signed_refl (a : α) : C.Signed a a := Or.inl (C.refl a)

theorem signed_of_rel {a b : α} (h : C.rel a b) : C.Signed a b := Or.inl h

theorem signed_symm {a b : α} (h : C.Signed a b) : C.Signed b a := by
  cases h with
  | inl h => exact Or.inl (C.symm h)
  | inr h =>
    have h' : C.rel (C.neg a) b := by
      simpa only [C.neg_neg] using C.neg_rel h
    exact Or.inr (C.symm h')

theorem signed_trans {a b c : α} (hab : C.Signed a b) (hbc : C.Signed b c) :
    C.Signed a c := by
  cases hab with
  | inl hab =>
    cases hbc with
    | inl hbc => exact Or.inl (C.trans hab hbc)
    | inr hbc => exact Or.inr (C.trans hab hbc)
  | inr hab =>
    cases hbc with
    | inl hbc => exact Or.inr (C.trans hab (C.neg_rel hbc))
    | inr hbc =>
      have h' : C.rel (C.neg b) c := by
        simpa only [C.neg_neg] using C.neg_rel hbc
      exact Or.inl (C.trans hab h')

theorem signed_neg_right_iff {a b : α} :
    C.Signed a (C.neg b) ↔ C.Signed a b := by
  constructor
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr h => exact Or.inl (by simpa only [C.neg_neg] using h)
  · intro h
    cases h with
    | inl h => exact Or.inr (by simpa only [C.neg_neg] using h)
    | inr h => exact Or.inl h

theorem signed_neg_left_iff {a b : α} :
    C.Signed (C.neg a) b ↔ C.Signed a b := by
  constructor
  · intro h
    exact C.signed_symm ((C.signed_neg_right_iff).mp (C.signed_symm h))
  · intro h
    exact C.signed_symm ((C.signed_neg_right_iff).mpr (C.signed_symm h))

/-- An absolute-value representative can be introduced from its sign cases. -/
theorem signed_of_sign_cases {a b : α} (h : a = b ∨ a = C.neg b) :
    C.Signed a b := by
  cases h with
  | inl h => subst a; exact Or.inl (C.refl b)
  | inr h => subst a; exact Or.inr (C.refl (C.neg b))

/-- The Pell application's bookkeeping is three transitive transports. -/
theorem residue_transport {u J s p : α}
    (huJ : C.Signed u J) (hus : C.Signed u s) (hsp : C.Signed s p) :
    C.Signed J p :=
  C.signed_trans (C.signed_trans (C.signed_symm huJ) hus) hsp

#print axioms signed_trans
#print axioms signed_neg_left_iff
#print axioms signed_of_sign_cases
#print axioms residue_transport

end Congruence

/-- Integer congruence, defined using only core's Euclidean remainder. -/
def intModulo (m : Int) : Congruence Int where
  rel a b := a % m = b % m
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂
  neg a := -a
  neg_neg := Int.neg_neg
  neg_rel := by
    intro a b h
    have ha := Int.sub_emod 0 a m
    have hb := Int.sub_emod 0 b m
    simp only [Int.zero_emod, Int.zero_sub] at ha hb
    exact ha.trans ((congrArg (fun z : Int => (-z) % m) h).trans hb.symm)

/-- Exact integer version of the sign bookkeeping needed in the Pell proof. -/
theorem int_residue_transport (m u J s p : Int)
    (huJ : u % m = J % m ∨ u % m = (-J) % m)
    (hus : u % m = s % m ∨ u % m = (-s) % m)
    (hsp : s % m = p % m ∨ s % m = (-p) % m) :
    J % m = p % m ∨ J % m = (-p) % m :=
  (intModulo m).residue_transport huJ hus hsp

/-- Changing an integer to its natural absolute-value representative is free
once congruences are interpreted up to sign. -/
theorem int_natAbs_transport (m a b : Int)
    (h : a % m = b % m ∨ a % m = (-b) % m) :
    (a.natAbs : Int) % m = b % m ∨ (a.natAbs : Int) % m = (-b) % m :=
  (intModulo m).signed_trans
    ((intModulo m).signed_symm
      ((intModulo m).signed_of_sign_cases (Int.natAbs_eq a))) h

#print axioms intModulo
#print axioms int_residue_transport
#print axioms int_natAbs_transport

end ProofSimplification.SignOrbit
