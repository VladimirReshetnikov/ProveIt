import DiophantineConsistency.BFS943.Direct80RankExact
import DiophantineConsistency.BFS943.Direct80NaturalProjection
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Projection quotient and main norm for the exact graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80ProjectionPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80RankExact TenPositive80NaturalProjection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_projection_pell (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    let a := A p v-1
    let R := rankNat p v
    let H := Hnat p v
    ∃ d z : V, d=Exp.exp R+a*(c p v)+H*z ∧
      d*d=1+(a*a+H)*(c p v)*(c p v) ∧ H∣b p v*Knat p v := by
  let a : V := A p v-1
  let R : V := rankNat p v
  let H : V := Hnat p v
  have hc : c p v=ycoord R a := (graph_rank_exact p v hb hl hh hv hz).2.2.2
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hA : 0<A p v := mul_pos (mul_pos hmu hY) (add_pos hX (by simp))
  have hA1 : a+1=A p v := tsub_add_cancel_of_le (pos_iff_one_le.mp hA)
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hH1 : H+1=4*A p v := tsub_add_cancel_of_le h4A
  have hH : H=4*a+3 := by
    apply add_right_cancel (b:=(1:V))
    calc
      H+1=4*A p v := hH1
      _=4*(a+1) := by rw [hA1]
      _=(4*a+3)+1 := by ring
  have hdelta : ArithmeticPellRecurrence.delta a=a*a+H := by rw [hH]; unfold ArithmeticPellRecurrence.delta; ring
  obtain ⟨z,hzq⟩ := projection_quotient a R
  refine ⟨xcoord R a,z,?_,?_,graph_natural_projection p v hb hv hz⟩
  · change xcoord R a=Exp.exp R+a*c p v+H*z
    rw [hH,hc]
    exact hzq
  · change xcoord R a*xcoord R a=1+(a*a+H)*(c p v)*(c p v)
    have hn := norm R a
    rwa [hdelta,←hc] at hn

#print axioms TenPositive80ProjectionPell.graph_projection_pell
end TenPositive80ProjectionPell
