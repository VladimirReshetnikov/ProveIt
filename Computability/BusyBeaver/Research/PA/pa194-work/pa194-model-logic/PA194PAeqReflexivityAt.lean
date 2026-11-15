import PA194PAeqAddOneAt
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.Reflexivity
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

def body : Semiproposition language 1 := eq (.bvar 0) (.bvar 0)
theorem source_mem : reflexivity.univCl ∈ ordinaryPAeq :=
  ⟨reflexivity, .fixed _ (by simp [fixedAxioms]), rfl⟩
theorem source_quote : (⌜reflexivity.univCl⌝ : V) = ^∀ (⌜body⌝ : V) := by
  have h : reflexivity.freeVariables = ∅ := by decide
  rw [Sentence.quote_def]
  rw [show (reflexivity.univCl : AddOne.Fm) = reflexivity from AddOne.coe_closed _ h]
  change (⌜(Semiformula.all body)⌝ : V) = _
  exact Semiformula.quote_all _

noncomputable def atTerm (t : Term V language) :
    (ordinaryPAeq.internalize V) ⊢! (⌜body⌝ : Semiformula V language 1).subst ![t] := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Semiformula V language 1 := ⌜body⌝
  have hd : T ⊢!ᵈᵉʳ insert (∀⁰ p) ∅ := by
    refine ⟨axm {⌜reflexivity.univCl⌝} ⌜reflexivity.univCl⌝, ?_⟩
    have h := (target_axiom_witness ordinaryPAeq reflexivity.univCl source_mem :
      Proof ordinaryPAeq (axm {⌜reflexivity.univCl⌝} ⌜reflexivity.univCl⌝ : V) ⌜reflexivity.univCl⌝)
    simpa [T,p,source_quote,Proof,Semiformula.quote_def,← singleton_eq_insert] using h
  exact paeqSpecializeProof T ∅ p t hd

noncomputable def atTermCode (t : V) : V :=
  paeqSpecializeCode (⌜body⌝ : V) t 0 (axm {⌜reflexivity.univCl⌝} ⌜reflexivity.univCl⌝)

theorem atTerm_val (t : Term V language) : (atTerm t).val = atTermCode t.val := by rfl

theorem atTermCode_valid {t : V} (ht : IsSemiterm language 0 t) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (atTermCode t) (substs1 language t (⌜body⌝ : V)) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  let q : Term V language := ⟨t,ht⟩
  have h := (atTerm q).derivationOf
  simpa [atTerm_val, atTermCode, q, Proof, substs1, Semiformula.quote_def,
    SemitermVec.val_succ, ← singleton_eq_insert] using h

instance atTermCode_definable : 𝚺₁-Function₁ (atTermCode : V → V) := by
  haveI : 𝚺₁-Function₄ (paeqSpecializeCode : V → V → V → V → V) := paeqSpecializeGraph_defined.to_definable
  unfold atTermCode
  rw [Semiformula.quote_eq_encode, Sentence.quote_eq_encode]
  definability

#print axioms atTermCode_valid
#print axioms atTermCode_definable
#print axioms source_mem
#print axioms source_quote
#print axioms atTerm
end PA194PAeq.Reflexivity
