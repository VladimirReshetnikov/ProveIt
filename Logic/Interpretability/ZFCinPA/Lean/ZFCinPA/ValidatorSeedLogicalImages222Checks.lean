import ZFCinPA.ValidatorSeedLogicalImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedLogicalImages222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222 ValidatorSeedMarkerDischarge222
open ValidatorSeedMarkerRelativization222 ValidatorSeedLogicalImages222
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)=qqAlls (reflBody (V := V)).val 1 := refl_binding
example : (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)=qqAlls (symmBody (V := V)).val 2 := symm_binding
example : (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)=qqAlls (transBody (V := V)).val 3 := trans_binding
example : (⌜(Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)=
    qqAlls (relExtBody (V := V) Language.Eq.eq).val 4 := relExt_binding _
example : (⌜(Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V)=
    qqAlls (relExtBody (V := V) Language.Mem.mem).val 4 := relExt_binding _
example : (⌜irreflexiveSentence⌝ : V)=qqAlls (irBody (V := V)).val 1 := ir_binding

-- The exact four-slot conjunction keeps its terminal truth; NNF implication
-- retains the dual terminal falsity instead of silently dropping it.
example (r : (ℒₛₑₜ).Rel 2) : relExtBody (V := V) r=
    (ValidatorEqualityImages222.eqAtom 0 2 ⋏
      (ValidatorEqualityImages222.eqAtom 1 3 ⋏ ⊤)) 🡒
    Semiformula.rel r ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] 🡒
    Semiformula.rel r ![Bootstrapping.Semiterm.bvar 2,Bootstrapping.Semiterm.bvar 3] := by
  simp [relExtBody,ValidatorEqualityImages222.eqAtom,ValidatorEqualityImages222.neqAtom,
    Bootstrapping.Semiformula.imp_def]
example : irBody (V := V)=ValidatorEqualityImages222.nmemAtom 0 0 ⋎ ⊥ := rfl

example (j : V) : Provable seedTheory (imp ℒₛₑₜ (emptyCode j)
    (tagRel j (⌜(Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2) : SetTheorySentence)⌝ : V))) :=
  relExt_image _ j
example : Provable seedTheory (imp ℒₛₑₜ (emptyCode (0 : V))
    (tagRel 0 (⌜irreflexiveSentence⌝ : V))) := irreflexivity_image 0
example : Provable seedTheory (imp ℒₛₑₜ (emptyCode (0 : V))
    (tagRel 0 (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V))) := refl_image 0

example (p j : V) (hp : IsFormula ℒₛₑₜ p)
    (hmem : V ⊧/![p] ValidatorEqualityImages222.equalityDelta.ch.val) (hj : p<j) :
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))) :=
  axiomImages_equality p j hp hmem hj
example (p j : V) (hp : IsFormula ℒₛₑₜ p) (hmem : p∈logicalTheory.Δ₁Class) (hj : p<j) :
    Derivable seedTheory (insert (tagRel j p) (insert (emptyGuard j) (sideSet j))) :=
  axiomImages_logicalTheory p j hp hmem hj
example (h : Provable logicalTheory (^⊥ : V)) : Provable seedTheory (^⊥ : V) :=
  provable_falsum_of_logicalTheory h
example (h : Provable logicalTheory (^⊥ : V)) :
    ∃ d : V, _root_.SetTheory.BusyBeaver.ZFC.ArithmeticHistory222.value d=2 :=
  logicalTheory_refutation_witness h

#print axioms refl_binding
#print axioms symm_binding
#print axioms trans_binding
#print axioms relExt_binding
#print axioms ir_binding
#print axioms refl_image
#print axioms symm_image
#print axioms trans_image
#print axioms relExt_image
#print axioms irreflexivity_image
#print axioms equality_image
#print axioms axiomImages_equality
#print axioms axiomImages_logicalTheory
#print axioms provable_falsum_of_logicalTheory
#print axioms logicalTheory_refutation_witness
end LeanProofs.ZFCinPA.ValidatorSeedLogicalImages222Checks
