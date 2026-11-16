import PA194ForwardFormulaCorrect
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardIdentityQuote
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open M6.PA.RelationalSource
open Ordinal (Term Formula)
open PA194ForwardTyped
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def NormalizedIdentityPacket (param : V) : Prop :=
  ParametersValid 0 0 param ∧ (∀ i < len (nth param 1), nth (nth param 1) i = ^&i) ∧
    nth param 2 = ^&(0 : V)

theorem identity_aligned {param : V} (h : NormalizedIdentityPacket param) :
    Aligned param (Fin.elim0 : Fin 0 → Term 0) (fun i : Nat => (.fvar i : Term 0)) (.fvar 0) := by
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i hi
    simpa [Semiterm.quote_def] using h.2.1 (i : V) hi
  · simpa [Semiterm.quote_def] using h.2.2

theorem identity_translate_quote (p : SourceFormula 0) {param : V}
    (h : NormalizedIdentityPacket param) (hlen : (⌜p⌝ : V) < len (nth param 1)) :
    translateFormula param (⌜p⌝ : V) =
      (⌜formula p (Fin.elim0 : Fin 0 → Term 0) (fun i : Nat => (.fvar i : Term 0))⌝ : V) :=
  formula_quote p _ _ _ _ (identity_aligned h) hlen


theorem normalizedIdentityPacket_exists (L : V) :
    ∃ param : V, NormalizedIdentityPacket param ∧ len (nth param 1) = L := by
  obtain ⟨v,hlen,hv⟩ := sigmaOne_skolem_vec (R := fun i y : V => y = ^&i) (by definability)
    (l := L) (fun i _ => ⟨_,rfl⟩)
  refine ⟨parameters 0 v (^&(0 : V)),⟨?_,?_,?_⟩,by simpa using hlen⟩
  · unfold ParametersValid
    simp only [parameters_bound,parameters_free,parameters_result]
    refine ⟨by simp,?_,by simp⟩
    refine IsSemitermVec.iff.mpr ⟨rfl,?_⟩
    intro i hi
    rw [hv i (by simpa [hlen] using hi)]
    simp
  · intro i hi
    simp only [parameters_free] at hi ⊢
    exact hv i (by simpa [hlen] using hi)
  · simp [parameters_result]

open PA194PAeq

theorem reflexivity_env : formula PA194PAeq.reflexivity (Fin.elim0 : Fin 0 → Term 0)
    (fun i : Nat => (.fvar i : Term 0)) =
  formula PA194PAeq.reflexivity Fin.elim0 (fun _ : Nat => (.fvar 0 : Term 0)) := rfl

theorem zeroNotSucc_env : formula PA194PAeq.zeroNotSucc (Fin.elim0 : Fin 0 → Term 0)
    (fun i : Nat => (.fvar i : Term 0)) =
  formula PA194PAeq.zeroNotSucc Fin.elim0 (fun _ : Nat => (.fvar 0 : Term 0)) := rfl

theorem addZero_env : formula PA194PAeq.addZero (Fin.elim0 : Fin 0 → Term 0)
    (fun i : Nat => (.fvar i : Term 0)) =
  formula PA194PAeq.addZero Fin.elim0 (fun _ : Nat => (.fvar 0 : Term 0)) := rfl

theorem mulZero_env : formula PA194PAeq.mulZero (Fin.elim0 : Fin 0 → Term 0)
    (fun i : Nat => (.fvar i : Term 0)) =
  formula PA194PAeq.mulZero Fin.elim0 (fun _ : Nat => (.fvar 0 : Term 0)) := rfl

theorem symmetry_env : formula PA194PAeq.symmetry (Fin.elim0 : Fin 0 → Term 0)
    (fun i : Nat => (.fvar i : Term 0)) =
  formula PA194PAeq.symmetry Fin.elim0 (fun _ : Nat => (.fvar 0 : Term 0)) := rfl
#print axioms normalizedIdentityPacket_exists
#print axioms identity_aligned
#print axioms identity_translate_quote
#print axioms reflexivity_env
#print axioms zeroNotSucc_env
#print axioms addZero_env
#print axioms mulZero_env
#print axioms symmetry_env
end generic
end PA194ForwardIdentityQuote
