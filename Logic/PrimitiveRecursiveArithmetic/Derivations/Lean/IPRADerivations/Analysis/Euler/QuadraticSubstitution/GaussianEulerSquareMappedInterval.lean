import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareTimeGeometry
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureSquarePartition

/-!
# Bounds for the image of a compact Euler interval under a rational square

The exact squared-grid encoding is an admissible original Euler interval.
The finite partition error has a fixed dyadic envelope whenever both the
mesh size and the observation denominator dominate the dyadic budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareMappedInterval

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianRationalQuadratureSquarePartition (lowerNumerator widthNumerator intervalDenominator)
open GaussianEulerSquareTimeGeometry (upperEndpoint)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B a C E T c d : PTm n) : Fm PTm n := intervalSource z R B a C E T ⋏ (le one c ⋏ le one d)

ipra_subst source

theorem original_interval (z R B a C E T c d : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T c d) :
    Γ ⊢[PRAAx] intervalSource z R B (lowerNumerator c a) (widthNumerator c a C) (intervalDenominator d E)
      (upperEndpoint c T) := by
  have base := GaussianEulerSquareTimeGeometry.mapped_source z R B E c d (.andI h.andE₁.andE₁ h.andE₂)
  have ha := h.andE₁.andE₂.andE₁
  have hc := h.andE₂.andE₁
  have hd := h.andE₂.andE₂
  have hsq := le_mul_mono h.andE₁.andE₂.andE₂ h.andE₁.andE₂.andE₂
  have grown : Γ ⊢[PRAAx] le ((c*((E*T)*(E*T)))*one) ((c*((E*T)*(E*T)))*d) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (c*((E*T)*(E*T))) hd)
  have squareTop : Γ ⊢[PRAAx] le (c*((a+C)*(a+C))) (c*((E*T)*(E*T))) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right c hsq)
  have top : Γ ⊢[PRAAx] le (c*((a+C)*(a+C))) ((intervalDenominator d E)*(upperEndpoint c T)) :=
    le_trans squareTop (le_congr (by ipra_ring) (by unfold intervalDenominator upperEndpoint; ipra_ring) grown)
  exact .andI base (.andI (positive_product _ _ (positive_product _ _ hc ha) ha)
    (le_congr (by unfold lowerNumerator widthNumerator; ipra_ring) (.eqRefl _) top))

theorem partition_budget (H L F N U V : PTm n)
    (hF : Γ ⊢[PRAAx] le one F) (hN : Γ ⊢[PRAAx] le U N) (hV : Γ ⊢[PRAAx] le U V) :
    Γ ⊢[PRAAx] le ((H*(L*H*V+two*(F*N)))*U) ((H*(L*H+two))*(F*(F*N*V))) := by
  have firstBound : Γ ⊢[PRAAx] le U (F*(F*N)) := by
    have useF : Γ ⊢[PRAAx] le (one*N) ((F*F)*N) :=
      mul_le_mul_right N (positive_product _ _ hF hF)
    exact le_trans hN (le_congr (one_mul N) (by ipra_ring) useF)
  have secondBound : Γ ⊢[PRAAx] le U (F*V) :=
    le_trans hV (le_congr (one_mul V) (.eqRefl _) (mul_le_mul_right V hF))
  have first : Γ ⊢[PRAAx] le (((L*H)*V)*U) ((L*H)*(F*(F*N*V))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right ((L*H)*V) firstBound)
  have second : Γ ⊢[PRAAx] le ((two*(F*N))*U) (two*(F*(F*N*V))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*(F*N)) secondBound)
  exact le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right H (add_le_add₂ first second))

theorem jacobian_budget (c C M d E N U : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le U N) :
    Γ ⊢[PRAAx] le ((c*C*C*M)*U) ((c*C*C*M)*(d*E*E*N)) := by
  have positive := positive_product _ _ (positive_product _ _ hd hE) hE
  exact le_congr (mul_comm _ _) (mul_comm _ _)
    (mul_le_mul_right (c*C*C*M) (le_trans hN
      (le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N positive))))

theorem actual_original_quadratic_image_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      intervalSource (var 0) (var 1) (var 2) (lowerNumerator (var 7) (var 3)) (widthNumerator (var 7) (var 3) (var 4))
        (intervalDenominator (var 8) (var 5)) (upperEndpoint (var 7) (var 6))) :=
  closeUniv 9 (.impI (original_interval _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareMappedInterval
