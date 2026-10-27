import ZFCinPA.ValidatorEqualityImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorEqualityImages222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorFormulaEncoder222 ValidatorEind222
open ValidatorEqualityImages222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal equality atom is Eind, with arbitrary total bound-stack access. -/
theorem equality_atom_exact (F B s : V) (i j : Fin 3) :
    encode F B s (eqAtom (V := V) i j).val = Eind B.[(i : V)] B.[(j : V)] :=
  encode_eqAtom F B s i j

theorem repeated_labels (F s a : V) :
    encode F (a∷a∷0) s (eqAtom (V := V) (1 : Fin 2) 0).val = Eind a a := by
  simpa using encode_eqAtom F (a∷a∷0) s (1 : Fin 2) 0

theorem refl_literal :
    (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ eqAtom 0 0 := rfl

theorem symm_literal :
    (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ (neqAtom 1 0 ⋎ eqAtom 0 1) := rfl

theorem trans_literal :
    (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) =
        ∀⁰ ∀⁰ ∀⁰ (neqAtom 2 1 ⋎ (neqAtom 1 0 ⋎ eqAtom 2 0)) := rfl

/-- Four binders, both relation inputs, and the terminal falsum are retained. -/
theorem relExt_mem_literal :
    (⌜(Rewriting.emb (Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2)) :
      SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqAtom 0 2 ⋎ (neqAtom 1 3 ⋎ ⊥)) ⋎
        (nmemAtom 0 1 ⋎ memAtom 2 3)) := rfl

theorem relExt_eq_literal :
    (⌜(Rewriting.emb (Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2)) :
      SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqAtom 0 2 ⋎ (neqAtom 1 3 ⋎ ⊥)) ⋎
        (neqAtom 0 1 ⋎ eqAtom 2 3)) := rfl

theorem recognizer_body : equalityDelta =
    Theory.Δ₁.ofFinite (𝗘𝗤 ℒₛₑₜ : SetTheory) Theory.EqAxiom.finite := rfl

theorem internal_equality_member {p : V}
    (hp : V ⊧/![p] equalityDelta.ch.val) :
    ∃ σ ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory), p=⌜σ⌝ :=
  mem_ch_ofFinite _ Theory.EqAxiom.finite hp

theorem zero_stream_no_freshness (F : V) :
    CProv (encode F 0 0 (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)) :=
  trans_image F 0

theorem irreflexivity_at_zero : CProv (wim (wel (0 : V) 0) 1) := not_mem_self 0

theorem equality_only_internal_refutation [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] :
    letI := equalityDelta
    Provable (𝗘𝗤 ℒₛₑₜ : SetTheory) (^⊥ : V) →
      ∃ code : V, ArithmeticHistory222.value code=2 := equality_refutation_witness

#print axioms encode_eqAtom
#print axioms encode_memAtom
#print axioms refl_image
#print axioms symm_image
#print axioms trans_image
#print axioms relExt_mem_image
#print axioms relExt_eq_image
#print axioms mem_ch_ofList
#print axioms mem_ch_ofFinite
#print axioms axOK_equality
#print axioms not_mem_self
#print axioms irreflexivity_image
#print axioms equality_refutation_witness
#print axioms equality_atom_exact
#print axioms repeated_labels
#print axioms refl_literal
#print axioms symm_literal
#print axioms trans_literal
#print axioms relExt_mem_literal
#print axioms relExt_eq_literal
#print axioms recognizer_body
#print axioms internal_equality_member
#print axioms zero_stream_no_freshness
#print axioms irreflexivity_at_zero
#print axioms equality_only_internal_refutation
end LeanProofs.ZFCinPA.ValidatorEqualityImages222Checks
