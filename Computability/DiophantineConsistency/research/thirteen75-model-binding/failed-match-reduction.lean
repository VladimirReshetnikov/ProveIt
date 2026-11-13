import DiophantineConsistency.Thirteen75Nodes
import DiophantineConsistency.ModelThirteenSquares
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace Thirteen75Cuts
open DiophantineConsistency Thirteen75Nodes
open ModelThirteenSquares ModelThirteenStrong ModelThirteenRestoration
variable {R : Type*} [CommRing R]

theorem scalar_eq (p : Fin 4 → R) (v : Fin 13 → R) :
    node_polynomial p v = value75 p v := by
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
  simp only [value75,aux77,normalAux,yLV,mixL,G,data,parent,b,Carrier65.core,Carrier65.strong]
  rw [hb,hq,hX,hY,hE,hk,hell,hc,ha,hH,hdelta,hD,hrank,htau,hV,hG,hy,hP,hQ,hZ,hU]
  dsimp only [node_polynomial,node_sumSquares,node_sumPQ_U,node_sqPQ,node_sqU,node_sqZ,node_product0]
  ring
end Thirteen75Cuts
#print axioms Thirteen75Cuts.scalar_eq
