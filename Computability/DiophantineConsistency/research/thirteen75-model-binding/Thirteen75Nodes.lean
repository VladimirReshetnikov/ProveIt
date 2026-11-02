import DiophantineConsistency.ModelDifferenceRing

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
noncomputable section
namespace Thirteen75Nodes
open DiophantineConsistency AdaptiveEquationSyntax2011

section Generic
variable {R : Type*} [Add R] [Sub R] [Mul R] [OfNat R 1] [OfNat R 3] [OfNat R 4]
def node_qm (p : Fin 4 → R) (v : Fin 13 → R) : R := (p 0) * (v 0)
def node_q (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_qm p v) + 1
def node_q2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_q p v) * (node_q p v)
def node_q3 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_q2 p v) * (node_q p v)
def node_X (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 7) * (node_q p v)
def node_Y (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 6) * (node_q3 p v)
def node_E (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_X p v) * (node_Y p v)
def node_k (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 9) + (v 10)
def node_kY (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_k p v) * (node_Y p v)
def node_ell (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_E p v) * (node_kY p v)
def node_c (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_kY p v) + (v 9)
def node_a (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_E p v) + (node_Y p v)
def node_four_a (p : Fin 4 → R) (v : Fin 13 → R) : R := 4 * (node_a p v)
def node_H (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_four_a p v) + 3
def node_a2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_a p v) * (node_a p v)
def node_Delta (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_a2 p v) + (node_H p v)
def node_ac (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_a p v) * (node_c p v)
def node_main_base (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_X p v) + (node_ac p v)
def node_gammaH (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 12) * (node_H p v)
def node_main_root (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_main_base p v) + (node_gammaH p v)
def node_c2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_c p v) * (node_c p v)
def node_Dc2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Delta p v) * (node_c2 p v)
def node_main_square (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_main_root p v) * (node_main_root p v)
def node_N1 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_main_square p v) - (node_Dc2 p v)
def node_qF (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_q p v) - (v 1)
def node_C (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_qF p v) - (v 2)
def node_gap_product (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_qm p v) * (node_qF p v)
def node_gap (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_gap_product p v) + (v 2)
def node_q2minus1 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_q2 p v) - 1
def node_rproduct (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_gap p v) * (node_q2minus1 p v)
def node_qMF (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_q p v) * (p 3)
def node_maskfactor (p : Fin 4 → R) (v : Fin 13 → R) : R := (p 2) + (node_qMF p v)
def node_mask (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_maskfactor p v) * (v 0)
def node_R (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_rproduct p v) + (node_mask p v)
def node_En (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_E p v) * (v 8)
def node_tau_partial (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_En p v) + (node_k p v)
def node_tau (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_tau_partial p v) - (node_R p v)
def node_tau2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_tau p v) * (node_tau p v)
def node_ell_plus_k (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_ell p v) + (node_k p v)
def node_first_product (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_ell p v) * (node_ell_plus_k p v)
def node_N0 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_tau2 p v) - (node_first_product p v)
def node_Kw (p : Fin 4 → R) (v : Fin 13 → R) : R := (p 1) + (v 7)
def node_transport (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Kw p v) * (node_C p v)
def node_B (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_transport p v) - (v 1)
def node_f2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 3) * (v 3)
def node_cT (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_c p v) * (v 5)
def node_cTminusR (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_cT p v) - (node_R p v)
def node_f2inner (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_f2 p v) * (node_cTminusR p v)
def node_V (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_f2inner p v) - (node_c p v)
def node_hi (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_qm p v) * (v 4)
def node_hi2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_hi p v) * (node_hi p v)
def node_intermediate (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_hi2 p v) * (node_Dc2 p v)
def node_strong_term (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_intermediate p v) * (node_c2 p v)
def node_V2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_V p v) * (node_V p v)
def node_LV (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_cTminusR p v) * (node_V p v)
def node_LB (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_LV p v) * (node_B p v)
def node_mLB (p : Fin 4 → R) (v : Fin 13 → R) : R := (v 11) - (node_LB p v)
def node_h_mLB (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_qm p v) * (node_mLB p v)
def node_carrier (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_h_mLB p v) - (node_B p v)
def node_four_carrier (p : Fin 4 → R) (v : Fin 13 → R) : R := 4 * (node_carrier p v)
def node_y (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_four_carrier p v) + 1
def node_y2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_y p v) * (node_y p v)
def node_V2minusY2 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_V2 p v) - (node_y2 p v)
def node_f2minus1 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_f2 p v) - 1
def node_Theta (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Delta p v) * (node_f2minus1 p v)
def node_aux_product (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Theta p v) * (node_V2minusY2 p v)
def node_Na (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_aux_product p v) + (node_y2 p v)
def node_Z (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_f2 p v) - (node_strong_term p v)
def node_product0 (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_N0 p v) * (node_N1 p v)
def node_sqPQ (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_product0 p v) * (node_product0 p v)
def node_sqU (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Na p v) * (node_Na p v)
def node_sqZ (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_Z p v) * (node_Z p v)
def node_sumPQ_U (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_sqPQ p v) + (node_sqU p v)
def node_sumSquares (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_sumPQ_U p v) + (node_sqZ p v)
def node_polynomial (p : Fin 4 → R) (v : Fin 13 → R) : R := (node_sumSquares p v) - 3
end Generic

def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  node_polynomial (fun j => Expr.constant (p j)) Expr.var

section Eval
variable {R : Type*} [CommRing R]

theorem eval_qm (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_qm (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_qm (fun j => (p j : R)) v := by
  simp only [node_qm, Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var]

theorem eval_q (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_q (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_q (fun j => (p j : R)) v := by
  simp only [node_q, Expr.evalRing_add, eval_qm, Expr.evalRing_ofNat, Nat.cast_one]

theorem eval_q2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_q2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_q2 (fun j => (p j : R)) v := by
  simp only [node_q2, Expr.evalRing_mul, eval_q]

theorem eval_q3 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_q3 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_q3 (fun j => (p j : R)) v := by
  simp only [node_q3, Expr.evalRing_mul, eval_q2, eval_q]

theorem eval_X (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_X (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_X (fun j => (p j : R)) v := by
  simp only [node_X, Expr.evalRing_mul, Expr.evalRing_var, eval_q]

theorem eval_Y (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Y (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Y (fun j => (p j : R)) v := by
  simp only [node_Y, Expr.evalRing_mul, Expr.evalRing_var, eval_q3]

theorem eval_E (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_E (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_E (fun j => (p j : R)) v := by
  simp only [node_E, Expr.evalRing_mul, eval_X, eval_Y]

theorem eval_k (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_k (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_k (fun j => (p j : R)) v := by
  simp only [node_k, Expr.evalRing_add, Expr.evalRing_var]

theorem eval_kY (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_kY (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_kY (fun j => (p j : R)) v := by
  simp only [node_kY, Expr.evalRing_mul, eval_k, eval_Y]

theorem eval_ell (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_ell (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_ell (fun j => (p j : R)) v := by
  simp only [node_ell, Expr.evalRing_mul, eval_E, eval_kY]

theorem eval_c (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_c (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_c (fun j => (p j : R)) v := by
  simp only [node_c, Expr.evalRing_add, eval_kY, Expr.evalRing_var]

theorem eval_a (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_a (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_a (fun j => (p j : R)) v := by
  simp only [node_a, Expr.evalRing_add, eval_E, eval_Y]

theorem eval_four_a (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_four_a (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_four_a (fun j => (p j : R)) v := by
  simp only [node_four_a, Expr.evalRing_mul, Expr.evalRing_ofNat, Nat.cast_ofNat, eval_a]

theorem eval_H (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_H (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_H (fun j => (p j : R)) v := by
  simp only [node_H, Expr.evalRing_add, eval_four_a, Expr.evalRing_ofNat, Nat.cast_ofNat]

theorem eval_a2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_a2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_a2 (fun j => (p j : R)) v := by
  simp only [node_a2, Expr.evalRing_mul, eval_a]

theorem eval_Delta (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Delta (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Delta (fun j => (p j : R)) v := by
  simp only [node_Delta, Expr.evalRing_add, eval_a2, eval_H]

theorem eval_ac (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_ac (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_ac (fun j => (p j : R)) v := by
  simp only [node_ac, Expr.evalRing_mul, eval_a, eval_c]

theorem eval_main_base (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_main_base (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_main_base (fun j => (p j : R)) v := by
  simp only [node_main_base, Expr.evalRing_add, eval_X, eval_ac]

theorem eval_gammaH (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_gammaH (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_gammaH (fun j => (p j : R)) v := by
  simp only [node_gammaH, Expr.evalRing_mul, Expr.evalRing_var, eval_H]

theorem eval_main_root (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_main_root (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_main_root (fun j => (p j : R)) v := by
  simp only [node_main_root, Expr.evalRing_add, eval_main_base, eval_gammaH]

theorem eval_c2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_c2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_c2 (fun j => (p j : R)) v := by
  simp only [node_c2, Expr.evalRing_mul, eval_c]

theorem eval_Dc2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Dc2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Dc2 (fun j => (p j : R)) v := by
  simp only [node_Dc2, Expr.evalRing_mul, eval_Delta, eval_c2]

theorem eval_main_square (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_main_square (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_main_square (fun j => (p j : R)) v := by
  simp only [node_main_square, Expr.evalRing_mul, eval_main_root]

theorem eval_N1 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_N1 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_N1 (fun j => (p j : R)) v := by
  simp only [node_N1, Expr.evalRing_sub, eval_main_square, eval_Dc2]

theorem eval_qF (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_qF (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_qF (fun j => (p j : R)) v := by
  simp only [node_qF, Expr.evalRing_sub, eval_q, Expr.evalRing_var]

theorem eval_C (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_C (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_C (fun j => (p j : R)) v := by
  simp only [node_C, Expr.evalRing_sub, eval_qF, Expr.evalRing_var]

theorem eval_gap_product (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_gap_product (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_gap_product (fun j => (p j : R)) v := by
  simp only [node_gap_product, Expr.evalRing_mul, eval_qm, eval_qF]

theorem eval_gap (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_gap (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_gap (fun j => (p j : R)) v := by
  simp only [node_gap, Expr.evalRing_add, eval_gap_product, Expr.evalRing_var]

theorem eval_q2minus1 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_q2minus1 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_q2minus1 (fun j => (p j : R)) v := by
  simp only [node_q2minus1, Expr.evalRing_sub, eval_q2, Expr.evalRing_ofNat, Nat.cast_one]

theorem eval_rproduct (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_rproduct (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_rproduct (fun j => (p j : R)) v := by
  simp only [node_rproduct, Expr.evalRing_mul, eval_gap, eval_q2minus1]

theorem eval_qMF (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_qMF (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_qMF (fun j => (p j : R)) v := by
  simp only [node_qMF, Expr.evalRing_mul, eval_q, Expr.evalRing_constant]

theorem eval_maskfactor (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_maskfactor (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_maskfactor (fun j => (p j : R)) v := by
  simp only [node_maskfactor, Expr.evalRing_add, Expr.evalRing_constant, eval_qMF]

theorem eval_mask (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_mask (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_mask (fun j => (p j : R)) v := by
  simp only [node_mask, Expr.evalRing_mul, eval_maskfactor, Expr.evalRing_var]

theorem eval_R (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_R (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_R (fun j => (p j : R)) v := by
  simp only [node_R, Expr.evalRing_add, eval_rproduct, eval_mask]

theorem eval_En (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_En (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_En (fun j => (p j : R)) v := by
  simp only [node_En, Expr.evalRing_mul, eval_E, Expr.evalRing_var]

theorem eval_tau_partial (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_tau_partial (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_tau_partial (fun j => (p j : R)) v := by
  simp only [node_tau_partial, Expr.evalRing_add, eval_En, eval_k]

theorem eval_tau (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_tau (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_tau (fun j => (p j : R)) v := by
  simp only [node_tau, Expr.evalRing_sub, eval_tau_partial, eval_R]

theorem eval_tau2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_tau2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_tau2 (fun j => (p j : R)) v := by
  simp only [node_tau2, Expr.evalRing_mul, eval_tau]

theorem eval_ell_plus_k (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_ell_plus_k (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_ell_plus_k (fun j => (p j : R)) v := by
  simp only [node_ell_plus_k, Expr.evalRing_add, eval_ell, eval_k]

theorem eval_first_product (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_first_product (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_first_product (fun j => (p j : R)) v := by
  simp only [node_first_product, Expr.evalRing_mul, eval_ell, eval_ell_plus_k]

theorem eval_N0 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_N0 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_N0 (fun j => (p j : R)) v := by
  simp only [node_N0, Expr.evalRing_sub, eval_tau2, eval_first_product]

theorem eval_Kw (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Kw (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Kw (fun j => (p j : R)) v := by
  simp only [node_Kw, Expr.evalRing_add, Expr.evalRing_constant, Expr.evalRing_var]

theorem eval_transport (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_transport (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_transport (fun j => (p j : R)) v := by
  simp only [node_transport, Expr.evalRing_mul, eval_Kw, eval_C]

theorem eval_B (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_B (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_B (fun j => (p j : R)) v := by
  simp only [node_B, Expr.evalRing_sub, eval_transport, Expr.evalRing_var]

theorem eval_f2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_f2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_f2 (fun j => (p j : R)) v := by
  simp only [node_f2, Expr.evalRing_mul, Expr.evalRing_var]

theorem eval_cT (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_cT (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_cT (fun j => (p j : R)) v := by
  simp only [node_cT, Expr.evalRing_mul, eval_c, Expr.evalRing_var]

theorem eval_cTminusR (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_cTminusR (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_cTminusR (fun j => (p j : R)) v := by
  simp only [node_cTminusR, Expr.evalRing_sub, eval_cT, eval_R]

theorem eval_f2inner (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_f2inner (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_f2inner (fun j => (p j : R)) v := by
  simp only [node_f2inner, Expr.evalRing_mul, eval_f2, eval_cTminusR]

theorem eval_V (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_V (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_V (fun j => (p j : R)) v := by
  simp only [node_V, Expr.evalRing_sub, eval_f2inner, eval_c]

theorem eval_hi (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_hi (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_hi (fun j => (p j : R)) v := by
  simp only [node_hi, Expr.evalRing_mul, eval_qm, Expr.evalRing_var]

theorem eval_hi2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_hi2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_hi2 (fun j => (p j : R)) v := by
  simp only [node_hi2, Expr.evalRing_mul, eval_hi]

theorem eval_intermediate (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_intermediate (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_intermediate (fun j => (p j : R)) v := by
  simp only [node_intermediate, Expr.evalRing_mul, eval_hi2, eval_Dc2]

theorem eval_strong_term (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_strong_term (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_strong_term (fun j => (p j : R)) v := by
  simp only [node_strong_term, Expr.evalRing_mul, eval_intermediate, eval_c2]

theorem eval_V2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_V2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_V2 (fun j => (p j : R)) v := by
  simp only [node_V2, Expr.evalRing_mul, eval_V]

theorem eval_LV (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_LV (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_LV (fun j => (p j : R)) v := by
  simp only [node_LV, Expr.evalRing_mul, eval_cTminusR, eval_V]

theorem eval_LB (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_LB (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_LB (fun j => (p j : R)) v := by
  simp only [node_LB, Expr.evalRing_mul, eval_LV, eval_B]

theorem eval_mLB (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_mLB (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_mLB (fun j => (p j : R)) v := by
  simp only [node_mLB, Expr.evalRing_sub, Expr.evalRing_var, eval_LB]

theorem eval_h_mLB (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_h_mLB (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_h_mLB (fun j => (p j : R)) v := by
  simp only [node_h_mLB, Expr.evalRing_mul, eval_qm, eval_mLB]

theorem eval_carrier (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_carrier (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_carrier (fun j => (p j : R)) v := by
  simp only [node_carrier, Expr.evalRing_sub, eval_h_mLB, eval_B]

theorem eval_four_carrier (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_four_carrier (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_four_carrier (fun j => (p j : R)) v := by
  simp only [node_four_carrier, Expr.evalRing_mul, Expr.evalRing_ofNat, Nat.cast_ofNat, eval_carrier]

theorem eval_y (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_y (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_y (fun j => (p j : R)) v := by
  simp only [node_y, Expr.evalRing_add, eval_four_carrier, Expr.evalRing_ofNat, Nat.cast_one]

theorem eval_y2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_y2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_y2 (fun j => (p j : R)) v := by
  simp only [node_y2, Expr.evalRing_mul, eval_y]

theorem eval_V2minusY2 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_V2minusY2 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_V2minusY2 (fun j => (p j : R)) v := by
  simp only [node_V2minusY2, Expr.evalRing_sub, eval_V2, eval_y2]

theorem eval_f2minus1 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_f2minus1 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_f2minus1 (fun j => (p j : R)) v := by
  simp only [node_f2minus1, Expr.evalRing_sub, eval_f2, Expr.evalRing_ofNat, Nat.cast_one]

theorem eval_Theta (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Theta (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Theta (fun j => (p j : R)) v := by
  simp only [node_Theta, Expr.evalRing_mul, eval_Delta, eval_f2minus1]

theorem eval_aux_product (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_aux_product (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_aux_product (fun j => (p j : R)) v := by
  simp only [node_aux_product, Expr.evalRing_mul, eval_Theta, eval_V2minusY2]

theorem eval_Na (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Na (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Na (fun j => (p j : R)) v := by
  simp only [node_Na, Expr.evalRing_add, eval_aux_product, eval_y2]

theorem eval_Z (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_Z (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_Z (fun j => (p j : R)) v := by
  simp only [node_Z, Expr.evalRing_sub, eval_f2, eval_strong_term]

theorem eval_product0 (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_product0 (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_product0 (fun j => (p j : R)) v := by
  simp only [node_product0, Expr.evalRing_mul, eval_N0, eval_N1]

theorem eval_sqPQ (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_sqPQ (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_sqPQ (fun j => (p j : R)) v := by
  simp only [node_sqPQ, Expr.evalRing_mul, eval_product0]

theorem eval_sqU (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_sqU (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_sqU (fun j => (p j : R)) v := by
  simp only [node_sqU, Expr.evalRing_mul, eval_Na]

theorem eval_sqZ (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_sqZ (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_sqZ (fun j => (p j : R)) v := by
  simp only [node_sqZ, Expr.evalRing_mul, eval_Z]

theorem eval_sumPQ_U (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_sumPQ_U (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_sumPQ_U (fun j => (p j : R)) v := by
  simp only [node_sumPQ_U, Expr.evalRing_add, eval_sqPQ, eval_sqU]

theorem eval_sumSquares (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_sumSquares (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_sumSquares (fun j => (p j : R)) v := by
  simp only [node_sumSquares, Expr.evalRing_add, eval_sumPQ_U, eval_sqZ]

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (node_polynomial (fun j => Expr.constant (p j)) Expr.var).evalRing v =
      node_polynomial (fun j => (p j : R)) v := by
  simp only [node_polynomial, Expr.evalRing_sub, eval_sumSquares, Expr.evalRing_ofNat, Nat.cast_ofNat]

theorem eval_literal (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (literal p).evalRing v = node_polynomial (fun j => (p j : R)) v := eval_polynomial p v

end Eval
end Thirteen75Nodes
#print axioms Thirteen75Nodes.eval_literal
