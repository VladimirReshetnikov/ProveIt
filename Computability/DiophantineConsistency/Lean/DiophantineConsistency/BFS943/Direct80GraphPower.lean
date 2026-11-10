import DiophantineConsistency.BFS943.Direct80ProductPower
import DiophantineConsistency.BFS943.Direct80PowerFromHeight
import DiophantineConsistency.BFS943.Direct80VariableHeight
import DiophantineConsistency.BFS943.Direct80RankLower

/-! Full-product height and exact power at the 80 graph's recovered rank. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GraphPower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalProjection
open TenPositive80VariableHeight TenPositive80RankLower
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_product_height (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) :
    b p v*(X p v+Exp.exp (rankNat p v))*(Exp.exp (rankNat p v)*X p v+1)<Hnat p v := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  obtain ⟨r,_,hr,_,hpow⟩ := graph_variable_height p v hb hl hh hv hz hbetaodd
  have hlower := graph_rank_lower p v hbeta31 (hv 0) (hv 2) (hv 5)
  have hr15 := half_rank_ge_fifteen (rankNat p v) r hlower.2.2 hr
  have hbx : b p v≤X p v := le_of_lt (h_lt_X p v (hv 5))
  have hprod := Direct80ProductPower.whole_product_lt_power (X p v) (b p v) r hlower.2.1 hbx hr15
  rw [←hr] at hprod
  exact lt_trans hprod hpow

theorem graph_power (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) : X p v=Exp.exp (rankNat p v) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  exact Direct80PowerFromHeight.graph_power_of_height p v hb hl hh hv hz
    (graph_product_height p v hbeta31 hl hh hv hz hbetaodd)

#print axioms Direct80GraphPower.graph_product_height
#print axioms Direct80GraphPower.graph_power
end Direct80GraphPower
