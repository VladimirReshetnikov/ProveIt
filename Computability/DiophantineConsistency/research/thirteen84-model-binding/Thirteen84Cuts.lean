import DiophantineConsistency.Thirteen84Nodes
import DiophantineConsistency.ModelThirteenSquares
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Thirteen84Cuts
open DiophantineConsistency Thirteen84Nodes
open ModelThirteenSquares ModelThirteenStrong ModelThirteenRestoration
variable {R : Type*} [CommRing R]

theorem scalar_eq (p : Fin 4 → R) (v : Fin 13 → R) :
    node_polynomial p v = value84 p v := by
  have hb : p 0*v 0 = node_qm p v := rfl
  have hq : node_qm p v+1 = node_q p v := rfl
  have hX : v 7*node_q p v = node_X p v := rfl
  have hY : v 6*(node_q p v)^3 = node_Y p v := by
    dsimp only [node_Y,node_q3,node_q2]; ring
  have hE : node_X p v*node_Y p v = node_E p v := rfl
  have hk : v 9+v 10 = node_k p v := rfl
  have hell : node_E p v*node_k p v*node_Y p v = node_ell p v := by
    dsimp only [node_ell,node_kY]; ring
  have hc : node_k p v*node_Y p v+v 9 = node_c p v := rfl
  have ha : node_E p v+node_Y p v = node_a p v := rfl
  have hH : 4*node_a p v+3 = node_H p v := rfl
  have hdelta : (node_a p v)^2+node_H p v = node_Delta p v := by
    dsimp only [node_Delta,node_a2]; ring
  have hD : node_X p v+node_a p v*node_c p v+v 12*node_H p v = node_main_root p v := rfl
  have hrank : (node_qm p v*(node_q p v-v 1)+v 2)*((node_q p v)^2-1) +
      (p 2+node_q p v*p 3)*v 0 = node_R p v := by
    dsimp only [node_R,node_mask,node_maskfactor,node_qMF,node_rproduct,node_q2minus1,
      node_gap,node_gap_product,node_qF,node_q2]; ring
  have htau : node_E p v*v 8+node_k p v-node_R p v = node_tau p v := rfl
  have hV : (v 3)^2*(node_c p v*v 5-node_R p v)-node_c p v = node_V p v := by
    dsimp only [node_V,node_f2inner,node_cTminusR,node_cT,node_f2]; ring
  have hG : (p 1+v 7)*(node_q p v-v 1-v 2)-v 1 = node_B p v := rfl
  have hy : 1+4*(node_qm p v*(v 11-(node_c p v*v 5-node_R p v)*node_V p v*node_B p v)-node_B p v) = node_y p v := by
    dsimp only [node_y,node_four_carrier,node_carrier,node_h_mLB,node_mLB,node_LB,node_LV,node_cTminusR,node_cT]; ring
  have hP : (node_tau p v)^2-node_ell p v*(node_ell p v+node_k p v) = node_N0 p v := by
    dsimp only [node_N0,node_tau2,node_first_product,node_ell_plus_k]; ring
  have hQ : (node_main_root p v)^2-node_Delta p v*(node_c p v)^2 = node_N1 p v := by
    dsimp only [node_N1,node_main_square,node_Dc2,node_c2]; ring
  have hZ : (v 3)^2-node_Delta p v*(node_qm p v*v 4*(node_c p v)^2)^2 = node_Z p v := by
    dsimp only [node_Z,node_f2,node_strong_term,node_intermediate,node_hi2,node_hi,node_Dc2,node_c2]; ring
  have hU : node_Delta p v*((v 3)^2-1)*((node_V p v)^2-(node_y p v)^2)+(node_y p v)^2 = node_Na p v := by
    dsimp only [node_Na,node_aux_product,node_Theta,node_f2minus1,node_f2,node_V2minusY2,node_V2,node_y2]; ring
  have hDP : (data p v).P = node_N0 p v := by
    change (ThirteenCarrier.core p v).P = _
    dsimp only [ThirteenCarrier.core]
    rw [hb,hq,hX,hY,hE,hk,hell,hrank,htau,hP]
  have hDQ : (data p v).Q = node_N1 p v := by
    change (ThirteenCarrier.core p v).Q = _
    dsimp only [ThirteenCarrier.core]
    rw [hb,hq,hX,hY,hE,hk,hc,ha,hH,hdelta,hD,hQ]
  have hDdelta : (data p v).delta = node_Delta p v := by
    change (ThirteenCarrier.core p v).delta = _
    dsimp only [ThirteenCarrier.core]
    rw [hb,hq,hX,hY,hE,ha,hH,hdelta]
  have hDc : (data p v).c = node_c p v := by
    change (v 9+v 10)*(v 6*(p 0*v 0+1)^3)+v 9 = _
    rw [hb,hq,hY,hk,hc]
  have hDrank : (data p v).rank = node_R p v := by
    change (p 0*v 0*((p 0*v 0+1)-v 1)+v 2)*((p 0*v 0+1)^2-1)+(p 2+(p 0*v 0+1)*p 3)*v 0 = _
    rw [hb,hq,hrank]
  have hDV : (data p v).V = node_V p v := by
    change (v 3)^2*((data p v).c*v 5-(data p v).rank)-(data p v).c = _
    rw [hDc,hDrank]
    exact hV
  have hGdata : G p v = node_B p v := by
    change (p 1+v 7)*(node_q p v-v 1-v 2)-v 1 = _
    exact hG
  have hYdata : yLV p v = node_y p v := by
    change 1+4*(b p v*(v 11-((data p v).c*v 5-(data p v).rank)*(data p v).V*G p v)-G p v) = _
    rw [show b p v = node_qm p v from rfl,hDc,hDrank,hDV,hGdata]
    exact hy
  have hZdata : Carrier65.strong (data p v) = node_Z p v := by
    change (v 3)^2-(data p v).delta*((b p v*v 4)*(data p v).c^2)^2 = _
    rw [hDdelta,show b p v = node_qm p v from rfl,hDc]
    exact hZ
  have hUdata : aux77 p v = node_Na p v := by
    change (data p v).delta * ((v 3)^2-1) * ((data p v).V^2-yLV p v^2) + yLV p v^2 = _
    rw [hDdelta,hDV,hYdata]
    exact hU
  have h84aux : aux84 p v = node_correctedU p v := by
    change aux77 p v - 16*((b p v*v 5*G p v*(data p v).V)^2*(v 3)^2)*((data p v).P-1) = _
    rw [hUdata,show b p v = node_qm p v from rfl,hGdata,hDV,hDP]
    dsimp only [node_correctedU,node_correction,node_corrCoefficient,node_corr0,node_bTGV2,node_bTGV,node_bTG,node_bT,node_Pminus1,node_f2]
    ring
  change node_polynomial p v = ((data p v).P * (data p v).Q)^2 + (aux84 p v)^2 + (Carrier65.strong (data p v))^2 - 3
  rw [hDP,hDQ,h84aux,hZdata]
  dsimp only [node_polynomial,node_sumSquares,node_sumPQ_U,node_sqPQ,node_sqU,node_sqZ,node_product0]
  ring
theorem literal_value (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = value84 (fun j => (p j : R)) v := by
  rw [eval_literal, scalar_eq]

theorem literal_expression (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = (expressionAt84 p).evalRing v := by
  rw [literal_value, evalRing_expressionAt84]
section Model
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
variable {V : Type*} [CommSemiring V] [LinearOrder V] [IsStrictOrderedRing V]
  [CanonicallyOrderedAdd V]

theorem shifted_zero_equal (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (positiveShift (literal p)) v ↔
      InternalZero (positiveShift (expressionAt84 p)) v := by
  rw [internalZero_positiveShift, internalZero_positiveShift, internalZero_iff, internalZero_iff,
      literal_expression]

def currentLiteral : Expr (Fin 13) := positiveShift (literal CurrentWindowCarry2011.ports)
end Model
end Thirteen84Cuts
#print axioms Thirteen84Cuts.shifted_zero_equal
#print axioms Thirteen84Cuts.literal_expression
#print axioms Thirteen84Cuts.scalar_eq
