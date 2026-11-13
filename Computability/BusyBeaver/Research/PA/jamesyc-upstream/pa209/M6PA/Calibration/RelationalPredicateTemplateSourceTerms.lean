module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateFormulaValidity
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem termValue_sourceShift {s : Nat} (t : Term s) (b f x : V) :
    termValue (Rew.shift t) b (x∷f)=termValue t b f := by
  cases t with
  | bvar i => simp [termValue]
  | fvar i => simp [termValue,Nat.cast_add,Nat.cast_one]
  | func fn _ => nomatch fn

theorem termValue_bShift {s : Nat} (t : Term s) {n b f : V}
    (h : EnvironmentsValid (s:V) n b f) (hf : ∀i,t.FVar? i→(i:V)<len f) :
    termValue (Rew.bShift t) (bindBound b) (bindFree f)=termBShift L (termValue t b f) := by
  cases t with
  | bvar i =>
    simpa [termValue,bindBound,Nat.cast_add,Nat.cast_one] using
      NumericPAeqTerm.shiftTerms_nth h.1 (show (i:Nat)<(s:V) by exact_mod_cast i.isLt)
  | fvar i => exact NumericPAeqTerm.shiftTerms_nth h.2 (hf i (by simp))
  | func fn _ => nomatch fn

theorem termValue_sourceSubst {s r : Nat} (t : Term s) (σ : Fin s→Term r) (b c f : V)
    (hb : ∀i : Fin s,nth c (i:Nat)=termValue (σ i) b f) :
    termValue ((Rew.subst σ) t) b f=termValue t c f := by
  cases t with
  | bvar i => simpa [termValue] using (hb i).symm
  | fvar i => simp [termValue]
  | func fn _ => nomatch fn

theorem sourceSubst_bind_agreement {s r : Nat} (σ : Fin s→Term r) {n b c f : V}
    (h : EnvironmentsValid (r:V) n b f) (hc : IsSemitermVec L (s:V) n c)
    (hb : ∀i : Fin s,nth c (i:Nat)=termValue (σ i) b f)
    (hf : ∀j i,(σ j).FVar? i→(i:V)<len f) :
    ∀i : Fin (s+1), nth (bindBound c) (i:Nat)=
      termValue ((Semiterm.bvar 0 : Term (r+1)) :> (Rew.bShift ∘ σ) $ i) (bindBound b) (bindFree f) := by
  intro i
  cases i using Fin.cases with
  | zero => simp [bindBound,termValue]
  | succ i =>
    simp only [Matrix.cons_val_succ,Function.comp_apply]
    rw [termValue_bShift _ h (hf i)]
    simpa [bindBound,Nat.cast_add,Nat.cast_one,hb i] using
      NumericPAeqTerm.shiftTerms_nth hc (show ((i:Nat):V)<(s:V) by exact_mod_cast i.isLt)

#print axioms termValue_sourceShift
#print axioms termValue_bShift
#print axioms termValue_sourceSubst
#print axioms sourceSubst_bind_agreement
end M6.PA.RelationalPredicateTemplate

