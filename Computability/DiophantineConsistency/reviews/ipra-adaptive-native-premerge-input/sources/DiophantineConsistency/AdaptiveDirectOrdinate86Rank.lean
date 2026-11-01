import DiophantineConsistency.AdaptiveDirectOrdinate86Indices
import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011

/-! Actual 86-zero rank window and signed rank congruence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Rank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open ArithmeticAdaptiveMainCongruence2011 ArithmeticAdaptiveFactorThree2011
open ArithmeticAdaptiveRankCongruence2011 ArithmeticAdaptiveRankWindow2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86MainOrientation AdaptiveDirectOrdinate86Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem expressionAt_main_congruence86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : MainCongruence p v := by
  exact main_congruence_of_facts p v (expressionAt_transport_positive86 p v hb hv hz)
    (expressionAt_Y_quotient86 p v hb hv hz) (expressionAt_main_oriented86 p v hb hv hz)

theorem expressionAt_rank_congruence86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) : RankCongruence p v := by
  exact rank_congruence_of_main p v (expressionAt_main_congruence86 p v hb hv hz)

theorem expressionAt_rank_window86 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (expressionAt86 (fun j => (p j:ℤ))) v) :
    RankWindow p v := by
  have hg := (expressionAt_transport_positive86 p v hb hv hz).2
  have hgap : v 1+v 2<1+v 0*(p 0:V) := tsub_pos_iff_lt.mp hg
  exact scalar_rank_window _ _ _ _ _ _ _ hb (hv 0) (hv 1) (hv 2) hl hh (by ring) hgap

end DiophantineConsistency.AdaptiveDirectOrdinate86Rank
