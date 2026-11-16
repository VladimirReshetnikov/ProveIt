module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeEqualityTerm
@[expose] public section
/-! PAeq atom replacement; adapted from Foundation EquationalTheory (Apache-2.0)
with the actual target relation0 and paid finite equality leaves. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open _root_.FFL.FirstOrder.Entailment Entailment.FiniteContext
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def typedNe {n : Nat} (s t : Semiterm V Presentation.language n) : Semiformula V Presentation.language n := ∼typedEq s t
@[simp] theorem typedNe_val {n : Nat} (s t : Semiterm V Presentation.language n) :
    (typedNe s t).val=qqNRel 2 0 (s.val∷t.val∷0) := by
  simp [typedNe,equalityCode,neg_rel,Presentation.source_relations]
@[simp] theorem typedNe_subst {n m : Nat} (w : SemitermVec V Presentation.language n m) (s t : Semiterm V Presentation.language n) :
    (typedNe s t).subst w=typedNe (s.subst w) (t.subst w) := by simp [typedNe]
@[simp] theorem typedNe_shift {n : Nat} (s t : Semiterm V Presentation.language n) :
    (typedNe s t).shift=typedNe s.shift t.shift := by simp [typedNe]
local notation "U" => Presentation.ordinaryPAeq
local prefix:max "#'" => Semiterm.bvar (V:=V) (L:=Presentation.language)
local prefix:max "&'" => Semiterm.fvar (V:=V) (L:=Presentation.language)
local postfix:max "⇞" => Semiterm.shift
local infix:50 " ≐ₚ " => typedEq
local infix:50 " ≉ₚ " => typedNe

theorem equality_atom (t₁ t₂ u₁ u₂ : Term V Presentation.language) :
    (U).internalize V ⊢ (t₁ ≐ₚ t₂) 🡒 (u₁ ≐ₚ u₂) 🡒 (t₁ ≐ₚ u₁) 🡒 (t₂ ≐ₚ u₂) := by
  cl_prover [equality_symm (V:=V) t₁ t₂,equality_trans (V:=V) t₂ t₁ u₁,equality_trans (V:=V) t₂ u₁ u₂]
theorem equality_negative_atom (t₁ t₂ u₁ u₂ : Term V Presentation.language) :
    (U).internalize V ⊢ (t₁ ≐ₚ t₂) 🡒 (u₁ ≐ₚ u₂) 🡒 (t₁ ≉ₚ u₁) 🡒 (t₂ ≉ₚ u₂) := by
  unfold typedNe
  cl_prover [equality_symm (V:=V) t₁ t₂,equality_symm (V:=V) u₁ u₂,equality_atom (V:=V) t₂ t₁ u₂ u₁]
open scoped Classical in
lemma replace_eq (t u : Semiterm V Presentation.language 1) :
    (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t ≐ₚ u).subst ![#'1] 🡒 (t ≐ₚ u).subst ![#'0]) := by
  suffices
      (U).internalize V ⊢
        (&'1 ≐ₚ &'0) 🡒
        (t⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ≐ₚ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V Presentation.language) := [t⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'1], &'1 ≐ₚ &'0]
  suffices
      Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'0] ≐ₚ u⇞⇞.subst ![&'0] by
    apply deduct'
    apply deduct
    exact this
  have hh : Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'1] :=
    by_axm₀
  have ht : Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0] :=
    of' (term_replace' t⇞⇞ &'1 &'0) ⨀ by_axm₁
  have hu : Γ ⊢[(U).internalize V] u⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'0] :=
    of' (term_replace' u⇞⇞ &'1 &'0) ⨀ by_axm₁
  exact of'
    (equality_atom (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

lemma replace_ne (t u : Semiterm V Presentation.language 1) :
    (U).internalize V ⊢ ∀¹ ∀¹ ((#'1 ≐ₚ #'0) 🡒 (t ≉ₚ u).subst ![#'1] 🡒 (t ≉ₚ u).subst ![#'0]) := by
  suffices
      (U).internalize V ⊢
        (&'1 ≐ₚ &'0) 🡒
        (t⇞⇞.subst ![&'1] ≉ₚ u⇞⇞.subst ![&'1]) 🡒
        (t⇞⇞.subst ![&'0] ≉ₚ u⇞⇞.subst ![&'0]) by
    apply TProof.all₂!
    simpa [Bootstrapping.Semiformula.free, SemitermVec.q, Semiterm.shift_substs, Semiterm.substs_substs]
  let Γ : List (Formula V Presentation.language) := [t⇞⇞.subst ![&'1] ≉ₚ u⇞⇞.subst ![&'1], &'1 ≐ₚ &'0]
  suffices
      Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'0] ≉ₚ u⇞⇞.subst ![&'0] by
    apply deduct'
    apply deduct
    exact this
  have hh : Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'1] ≉ₚ u⇞⇞.subst ![&'1] :=
    by_axm₀
  have ht : Γ ⊢[(U).internalize V] t⇞⇞.subst ![&'1] ≐ₚ t⇞⇞.subst ![&'0] :=
    of' (term_replace' t⇞⇞ &'1 &'0) ⨀ by_axm₁
  have hu : Γ ⊢[(U).internalize V] u⇞⇞.subst ![&'1] ≐ₚ u⇞⇞.subst ![&'0] :=
    of' (term_replace' u⇞⇞ &'1 &'0) ⨀ by_axm₁
  exact of'
    (equality_negative_atom (t⇞⇞.subst ![&'1]) (t⇞⇞.subst ![&'0])
      (u⇞⇞.subst ![&'1]) (u⇞⇞.subst ![&'0]))
    ⨀ ht ⨀ hu ⨀ hh

#print axioms typedNe_val
#print axioms typedNe_subst
#print axioms typedNe_shift
#print axioms equality_atom
#print axioms equality_negative_atom
#print axioms replace_eq
#print axioms replace_ne
end M6.PA.FoundationPAeqCode
