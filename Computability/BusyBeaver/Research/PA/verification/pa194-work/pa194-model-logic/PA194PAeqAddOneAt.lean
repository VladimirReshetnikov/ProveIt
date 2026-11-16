import PA194PAeqSpecialization
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.AddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem result_quote : (⌜resultSentence⌝ : V) = ^∀ (⌜prop⌝ : V) := by
  have h : (Semiformula.all prop).freeVariables = ∅ := by decide
  rw [Sentence.quote_def]
  rw [show (resultSentence : Fm) = .all prop from coe_closed _ h]
  exact Semiformula.quote_all _

noncomputable def addOneAt (t : Term V language) :
    (ordinaryPAeq.internalize V) ⊢! (⌜prop⌝ : Semiformula V language 1).subst ![t] := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Semiformula V language 1 := ⌜prop⌝
  have hd : T ⊢!ᵈᵉʳ insert (∀⁰ p) ∅ := by
    refine ⟨(⌜(show ordinaryPAeq ⊢! resultSentence from addOneTheoryProof)⌝ : V), ?_⟩
    have h := (addOneProof_internal (V := V))
    simpa [T,p,result_quote,Proof,Semiformula.quote_def,← singleton_eq_insert] using h
  exact paeqSpecializeProof T ∅ p t hd

theorem addOneAt_val (t : Term V language) :
    (addOneAt t).val = paeqSpecializeCode (⌜prop⌝ : V) t.val 0
      (⌜(show ordinaryPAeq ⊢! resultSentence from addOneTheoryProof)⌝ : V) := by
  rfl
noncomputable def addOneAtCode (t : V) : V :=
  paeqSpecializeCode (⌜prop⌝ : V) t 0
    (⌜(show ordinaryPAeq ⊢! resultSentence from addOneTheoryProof)⌝ : V)

theorem addOneAtCode_valid {t : V} (ht : IsSemiterm language 0 t) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (addOneAtCode t) (substs1 language t (⌜prop⌝ : V)) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  let q : Term V language := ⟨t,ht⟩
  have h := (addOneAt q).derivationOf
  simpa [addOneAt_val, addOneAtCode, q, Proof, substs1, Semiformula.quote_def,
    SemitermVec.val_succ, ← singleton_eq_insert] using h

#print axioms addOneAtCode_valid
#print axioms addOneAt_val

#print axioms result_quote
#print axioms addOneAt
end PA194PAeq.AddOne
