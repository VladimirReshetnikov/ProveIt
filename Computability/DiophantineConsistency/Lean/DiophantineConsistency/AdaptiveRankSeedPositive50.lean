import DiophantineConsistency.AdaptiveNamedValues51
import DiophantineConsistency.AdaptiveDirectOrdinate86Transport

/-! The named rank seed is positive at positive 42-variable zeros. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveRankSeedPositive50
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Transport ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gap42 (p : Fin 4 → ℕ) (v : Fin 42 → V) (hb : 0<(p 0:V))
    (hv : ∀ i,0<v i) (hz : InternalZero (AdaptiveNamedValues42.literal (fun j => (p j:ℤ))) v) :
    v 1+v 2 < 1+v 0*(p 0:V) := by
  let v33 : Fin 33 → V := fun i => v (AdaptiveNamedValues42.embed i)
  let v26 : Fin 26 → V := fun i => v33 (AdaptiveNamedValues33.embed i)
  let v22 : Fin 22 → V := fun i => v26 (AdaptiveNamedValues26.embed i)
  let v17 : Fin 17 → V := fun i => v22 (AdaptiveNamedValues22.embed i)
  let v16 : Fin 16 → V := fun i => v17 (AdaptiveRankWitness17.embed i)
  let v15 : Fin 15 → V := fun i => v16 (AdaptiveMainScaleWitness16.embed i)
  let v14 : Fin 14 → V := fun i => v15 (AdaptiveScaleWitness15.embed i)
  let v13 : Fin 13 → V := fun i => v14 (AdaptiveSquareWitnessDirect14.embed i)
  have h33 := AdaptiveNamedValues42.literal_zero_project _ v hz
  have h26 := AdaptiveNamedValues33.literal_zero_project _ v33 h33
  have h22 := AdaptiveNamedValues26.literal_zero_project _ v26 h26
  have h17 := AdaptiveNamedValues22.literal_zero_project _ v22 h22
  have h16 := AdaptiveRankWitness17.literal_zero_project _ v17 h17
  have h15 := AdaptiveMainScaleWitness16.literal_zero_project _ v16 h16
  have h14 := AdaptiveScaleWitness15.literal_zero_project _ v15 h15
  have h13 := AdaptiveSquareWitnessDirect14.literal_zero_project _ v14 h14
  have h86 := (AdaptiveDirectOrdinateSquareSums.optimized_zero_iff_original _ v13).mp h13
  have hv13 : ∀ i : Fin 13,0<v13 i := by intro i; exact hv _
  have ht := expressionAt_transport_positive86 p v13 hb hv13 h86
  have hg : 0<(1+v13 0*(p 0:V))-(v13 1+v13 2) := ht.2
  have hg' := (tsub_pos_iff_lt).mp hg
  simpa [v13,v14,v15,v16,v17,v22,v26,v33,AdaptiveNamedValues42.embed,AdaptiveNamedValues33.embed,
    AdaptiveNamedValues26.embed,AdaptiveNamedValues22.embed,AdaptiveRankWitness17.embed,
    AdaptiveMainScaleWitness16.embed,AdaptiveScaleWitness15.embed,AdaptiveSquareWitnessDirect14.embed] using hg'

theorem rank_rep (p : Fin 4 → ℕ) (v : Fin 42 → V) (hF : v 1≤1+v 0*(p 0:V)) :
    SignedRep (AdaptiveNamedValues51.expression1 (fun j => (p j:ℤ))) v
      (natural (v 2+((1+v 0*(p 0:V))-v 1)*(v 0*(p 0:V)))) := by
  have hb := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hq := rep_add_nat (rep_one v) hb
  exact rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hq (rep_var v 1) hF) hb)
end DiophantineConsistency.AdaptiveRankSeedPositive50
