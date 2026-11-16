module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeOpenInductionSupplier
@[expose] public section
/-! Discharge the original arbitrary-model induction branch. The exact source
closure count is retained; target canonical axioms use their own proved support
count, related by numeric surplus-vector agreement and actual proof opening. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem original_induction_axiom_supplier {c : V} (hc : InductionR (fun _=>True) c) :
    Provable Presentation.ordinaryPAeq (formulaCode 0 c) := by
  obtain ⟨m,b,k,hc,hb,hshift,hbv,hk,hbody⟩ := translated_induction_witness hc
  have hbm : IsSemiformula Presentation.language m b := ⟨hb,by rw [hbv]⟩
  obtain ⟨a,s,q,_,_,_,hq,hqshift,hqbody⟩ := additive_matrix_witness hbm hshift hbody
  have hi := open_successor_induction_provable hq hqshift
  rw [hqbody] at hi
  have ha := successor_proof_to_additive hk hi
  rw [hc]
  apply (provable_alls_iff_open hbm hshift).mpr
  simpa only [hbody] using ha

#print axioms original_induction_axiom_supplier
end M6.PA.FoundationPAeqCode

