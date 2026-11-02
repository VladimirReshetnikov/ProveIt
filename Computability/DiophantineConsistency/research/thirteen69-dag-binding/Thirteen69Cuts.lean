import DiophantineConsistency.Thirteen69Nodes
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Thirteen69Cuts
open DiophantineConsistency Thirteen69Nodes
variable {R : Type*} [CommRing R]

theorem scalar_eq (p : Fin 4 → R) (v : Fin 13 → R) :
    node_polynomial p v = ThirteenCarrier.value69 p v := by
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
  have hy : 1+4*(node_qm p v*(v 11-(node_V p v)^2*node_B p v)-node_B p v) = node_y p v := by
    dsimp only [node_y,node_four_carrier,node_carrier,node_h_mLB,node_mLB,node_LB,node_V2]; ring
  have hP : (node_tau p v)^2-node_ell p v*(node_ell p v+node_k p v) = node_N0 p v := by
    dsimp only [node_N0,node_tau2,node_first_product,node_ell_plus_k]; ring
  have hQ : (node_main_root p v)^2-node_Delta p v*(node_c p v)^2 = node_N1 p v := by
    dsimp only [node_N1,node_main_square,node_Dc2,node_c2]; ring
  have hS : node_Delta p v*(node_qm p v*v 4*(node_c p v)^2) = node_normalized_S p v := by
    dsimp only [node_normalized_S,node_hi,node_Dc2,node_c2]; ring
  simp only [ThirteenCarrier.value69,ThirteenCarrier.core]
  rw [hb,hq,hX,hY,hE,hk,hell,hc,ha,hH,hdelta,hD,hrank,htau,hV,hG,hy,hP,hQ,hS]
  dsimp only [node_polynomial,node_product4,node_product1,node_product0,node_Na,
    node_aux_product,node_V2minusY2,node_y2,node_V2,node_normalized_S2,node_scaled_Ns,
    node_scaled_f2,node_f2]
  ring
theorem literal_value (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = ThirteenCarrier.value69 (fun j => (p j : R)) v := by
  rw [eval_literal, scalar_eq]

section Model
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
variable {V : Type*} [CommSemiring V] [LinearOrder V] [IsStrictOrderedRing V]
  [CanonicallyOrderedAdd V]

theorem internal_zero (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (literal p) v ↔
      ThirteenCarrier.value69 (fun j => (p j : DiffRing V)) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff, literal_value]

theorem shifted_zero (p : Fin 4 → ℤ) (v : Fin 13 → V) :
    InternalZero (positiveShift (literal p)) v ↔
      ThirteenCarrier.value69 (fun j => (p j : DiffRing V)) (fun j => ι (v j+1)) = 0 := by
  rw [internalZero_positiveShift, internal_zero]

def currentLiteral : Expr (Fin 13) := positiveShift (literal CurrentWindowCarry2011.ports)

theorem current_zero (v : Fin 13 → V) :
    InternalZero currentLiteral v ↔
      ThirteenCarrier.value69 (fun j => (CurrentWindowCarry2011.ports j : DiffRing V))
        (fun j => ι (v j+1)) = 0 := shifted_zero _ v
end Model
end Thirteen69Cuts
#print axioms Thirteen69Cuts.scalar_eq
#print axioms Thirteen69Cuts.literal_value
#print axioms Thirteen69Cuts.internal_zero
#print axioms Thirteen69Cuts.shifted_zero
#print axioms Thirteen69Cuts.current_zero
