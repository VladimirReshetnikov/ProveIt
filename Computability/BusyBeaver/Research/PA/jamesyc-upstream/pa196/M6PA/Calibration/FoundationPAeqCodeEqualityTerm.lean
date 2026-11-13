module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeEqualityLeaves
public import Foundation.Meta.ClProver
@[expose] public section
/-! Adapted from Foundation Bootstrapping/DerivabilityCondition/EquationalTheory
(Apache-2.0). This is a new proof for PAeq's distinct zero/succ/add/mul signature,
not an application of the ordered-semiring replacement theorem. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open _root_.FFL.FirstOrder.Entailment Entailment.FiniteContext
open Bootstrapping.Semiformula
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Semiterm.bvar (V:=V) (L:=Presentation.language)
local prefix:max "&'" => Semiterm.fvar (V:=V) (L:=Presentation.language)
local postfix:max "⇞" => Semiterm.shift
local infix:50 " ≐ₚ " => typedEq
local infix:50 " ^=ₚ " => equalityCode
local infixl:65 " +ₚ " => typedAdd
local infixl:70 " *ₚ " => typedMul

private lemma vec2_eq {v : V} (h : len v=2) : ?[v.[0],v.[1]]=v :=
  nth_ext' 2 (by simp [one_add_one_eq_two]) h (by
    intro i hi
    have : i=0 ∨ i=1 := le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi)
    rcases this with rfl|rfl <;> simp)

open scoped Classical in
lemma term_replace_aux (t : V) :
    IsSemiterm Presentation.language 1 t →
    Provable U (^∀ ^∀ imp Presentation.language (^#1 ^=ₚ ^#0) (termSubst Presentation.language (^#1 ∷ 0) t ^=ₚ termSubst Presentation.language (^#0 ∷ 0) t))
      := by
  apply IsSemiterm.sigma1_induction
  · definability
  case hfunc =>
    intro k F v hF hv ih
    rcases (Presentation.source_functions k F).mp hF with (⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl|rfl⟩)
    · rcases show v = 0 by simpa using hv
      suffices
          (U).internalize V ⊢
            ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (typedZero.subst ![#'1] ≐ₚ typedZero.subst ![#'0]))
            by
        have := (tprovable_iff_provable (T := U)).mp this
        simpa [-typedZero_subst,val_all,equalityCode,zeroCode,Presentation.source_functions] using this
      suffices
        (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (typedZero ≐ₚ typedZero)) by simpa
      suffices (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 (typedZero ≐ₚ typedZero) by
        apply TProof.all₂!; simpa [Bootstrapping.Semiformula.free]
      apply Entailment.dhyp (equality_refl _)
    · let t : Semiterm V Presentation.language 1 := ⟨v.[0],by simpa using hv.nth (by simp)⟩
      have veq : v=t.val∷0 := by
        apply nth_ext' 1 hv.lh (by simp)
        intro i hi; have : i=0 := lt_one_iff_eq_zero.mp hi
        subst i; simp [t]
      suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ((typedSucc t).subst ![#'1] ≐ₚ (typedSucc t).subst ![#'0])) by
        have := (tprovable_iff_provable (T:=U)).mp this
        rw [veq]
        simpa [-typedSucc_subst,val_all,equalityCode] using! this
      let Γ : List (Formula V Presentation.language) := [&'1 ≐ₚ &'0]
      suffices Γ ⊢[(U).internalize V]
          typedSucc (t⇞⇞.subst ![&'1]) ≐ₚ typedSucc (t⇞⇞.subst ![&'0]) by
        apply TProof.all₂!
        simpa [Bootstrapping.Semiformula.free,SemitermVec.q,Semiterm.shift_substs,Semiterm.substs_substs]
      have iht : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t.subst ![#'1] ≐ₚ t.subst ![#'0])) := by
        apply (tprovable_iff_provable (T:=U)).mpr
        simpa [t] using ih 0 (by simp)
      have iht : Γ ⊢[(U).internalize V] (t⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0]) := by
        have := TProof.specialize₂_shift! iht &'0 &'1
        simpa [Semiterm.shift_substs,Semiterm.substs_substs] using! this
      exact of' (equality_succ _ _) ⨀ iht
    · let t : Semiterm V Presentation.language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V Presentation.language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices
          (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ((t +ₚ u).subst ![#'1] ≐ₚ (t +ₚ u).subst ![#'0])) by
        have := (tprovable_iff_provable (T := U)).mp this
        rw [veq]
        simpa [-typedAdd_subst,val_all,equalityCode] using! this
      let Γ : List (Formula V Presentation.language) := [&'1 ≐ₚ &'0]
      suffices
          Γ ⊢[(U).internalize V]
            t⇞⇞.subst ![&'1] +ₚ u⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0] +ₚ u⇞⇞.subst ![&'0] by
        apply TProof.all₂!;
        simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
      have iht : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t.subst ![#'1] ≐ₚ t.subst ![#'0])) := by
        apply (tprovable_iff_provable (T := U)).mpr
        simpa [t] using ih 0 (by simp)
      have ihu : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (u.subst ![#'1] ≐ₚ u.subst ![#'0])) := by
        apply (tprovable_iff_provable (T := U)).mpr
        simpa [u] using ih 1 (by simp)
      have iht : Γ ⊢[(U).internalize V] (t⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0]) := by
        have := TProof.specialize₂_shift! iht &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using! this
      have ihu : Γ ⊢[(U).internalize V] (u⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'0]) := by
        have := TProof.specialize₂_shift! ihu &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using! this
      have := equality_add (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
        (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0])
      exact of' this ⨀ iht ⨀ ihu
    · let t : Semiterm V Presentation.language 1 := ⟨v.[0], by simpa using hv.nth (by simp)⟩
      let u : Semiterm V Presentation.language 1 := ⟨v.[1], by simpa using hv.nth (by simp)⟩
      have veq : v = ?[t.val, u.val] := by simp [t, u, vec2_eq hv.lh]
      suffices
          (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 ((t *ₚ u).subst ![#'1] ≐ₚ (t *ₚ u).subst ![#'0])) by
        have := (tprovable_iff_provable (T := U)).mp this
        rw [veq]
        simpa [-typedMul_subst,val_all,equalityCode] using! this
      let Γ : List (Formula V Presentation.language) := [&'1 ≐ₚ &'0]
      suffices
          Γ ⊢[(U).internalize V]
            t⇞⇞.subst ![&'1] *ₚ u⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0] *ₚ u⇞⇞.subst ![&'0] by
        apply TProof.all₂!;
        simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
      have iht : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t.subst ![#'1] ≐ₚ t.subst ![#'0])) := by
        apply (tprovable_iff_provable (T := U)).mpr
        simpa [t] using ih 0 (by simp)
      have ihu : (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (u.subst ![#'1] ≐ₚ u.subst ![#'0])) := by
        apply (tprovable_iff_provable (T := U)).mpr
        simpa [u] using ih 1 (by simp)
      have iht : Γ ⊢[(U).internalize V] (t⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0]) := by
        have := TProof.specialize₂_shift! iht &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using! this
      have ihu : Γ ⊢[(U).internalize V] (u⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'0]) := by
        have := TProof.specialize₂_shift! ihu &'0 &'1
        simpa [Semiterm.shift_substs, Semiterm.substs_substs] using! this
      have := equality_mul (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
        (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0])
      exact of' this ⨀ iht ⨀ ihu
  case hbvar =>
    intro z hz
    have : z = 0 := lt_one_iff_eq_zero.mp hz
    rcases this with rfl
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (#'1 ≐ₚ #'0)) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [val_all,equalityCode] using this
    apply TProof.all₂!
    simp only [Semiformula.shift_imp,typedEq_shift,Semiformula.substs_imp,typedEq_subst]
    cl_prover

  case hfvar =>
    intro x
    suffices (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (&'x ≐ₚ &'x)) by
      have := (tprovable_iff_provable (T := U)).mp this
      simpa [val_all,equalityCode] using this
    suffices (U).internalize V ⊢ (&'1 ≐ₚ &'0) 🡒 (&'(x + 1 + 1) ≐ₚ &'(x + 1 + 1)) by
      apply TProof.all₂!; simpa [Bootstrapping.Semiformula.free]
    apply Entailment.dhyp (equality_refl _)

lemma term_replace (t : Semiterm V Presentation.language 1) :
    (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t.subst ![#'1] ≐ₚ t.subst ![#'0])) := by
  apply (tprovable_iff_provable (T := U)).mpr
  simpa using term_replace_aux t.val

lemma term_replace' (t : Semiterm V Presentation.language 1) (u₁ u₂ : Term V Presentation.language) :
    (U).internalize V ⊢ (u₁ ≐ₚ u₂) 🡒 (t.subst ![u₁] ≐ₚ t.subst ![u₂]) := by
  have := TProof.specialize₂! (term_replace t) u₂ u₁
  simpa [Semiterm.substs_substs] using this

#print axioms term_replace_aux
#print axioms term_replace
#print axioms term_replace'
end M6.PA.FoundationPAeqCode
