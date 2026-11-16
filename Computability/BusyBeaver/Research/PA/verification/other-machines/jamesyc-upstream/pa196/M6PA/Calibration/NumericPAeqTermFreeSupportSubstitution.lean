module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermFreeSupportLaws
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language
instance freeBound_definable' (Γ : Polarity) (k : Nat) : Γᴬ_[k+1]-Function₁ (freeBound : V→V) :=
  freeBound_definable.of_sigmaOne

theorem freeSupported_subst {s r l w t : V} (ht : IsSemiterm L s t)
    (hw : IsSemitermVec L s r w) (hs : FreeSupported l t)
    (hws : ∀ i<s, FreeSupported l (nth w i)) : FreeSupported l (termSubst L w t) := by
  have hall : ∀ t, IsSemiterm L s t → FreeSupported l t → FreeSupported l (termSubst L w t) := by
    intro a ha
    apply IsSemiterm.induction 𝚺 (P:=fun t : V => FreeSupported l t → FreeSupported l (termSubst L w t)) ?_ ?_ ?_ ?_ a ha
    · dsimp [FreeSupported]; definability
    · intro i hi _; simpa using hws i hi
    · intro i h; simpa using h
    · intro k f ts hf hv ih h
      rw [termSubst_func hf hv.isUTerm]
      apply (freeSupported_func hf (hw.termSubstVec hv).isUTerm).mpr
      intro i hi
      rw [nth_termSubstVec hv.isUTerm hi]
      exact ih i hi ((freeSupported_func hf hv.isUTerm).mp h i hi)
  exact hall t ht hs

#print axioms freeSupported_subst
end M6.PA.NumericPAeqTerm

