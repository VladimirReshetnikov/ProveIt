module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateLogicalRules
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
variable {T : Theory L} [T.Δ₁]
theorem template_cut {Γ Δ : LK.Sequent sourceLanguage} {p : Formula 0} {P f : V}
    (hP : IsSemiformula L 1 P) (hf : IsSemitermVec L (len f) 0 f)
    (hp : ∀i,p.FVar? i→(i:V)<len f)
    (dp : Derivable T (sequentValue (Γ+⦃p⦄) P f))
    (dn : Derivable T (sequentValue (Δ+⦃∼p⦄) P f)) :
    Derivable T (sequentValue (Γ+Δ) P f) := by
  rw [sequentValue_append_one] at dp dn
  have hn : formulaValue (∼p) P 0 f=neg L (formulaValue p P 0 f) :=
    formulaValue_neg p hP ⟨by simp,hf⟩ hp
  rw [hn] at dn
  have hpv := dp.isFormulaSet.insert.1
  have hΓ := dp.isFormulaSet.insert.2
  have hΔ := dn.isFormulaSet.insert.2
  rw [sequentValue_add]
  apply Derivable.cut (formulaValue p P 0 f)
  · exact Derivable.wk (by simp [hpv,hΓ,hΔ]) (by intro x hx; simp only [mem_bitInsert_iff,mem_cup_iff] at *; tauto) dp
  · exact Derivable.wk (by simp [hpv,hΓ,hΔ]) (by intro x hx; simp only [mem_bitInsert_iff,mem_cup_iff] at *; tauto) dn
#print axioms template_cut
end M6.PA.RelationalPredicateTemplate

