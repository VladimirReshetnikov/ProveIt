import IPRADerivations.Analysis.FiniteOperations.GaussianPositiveScalarProductBound

/-!
# Transfer a product norm through an exact scalar radius

The actual reference represents W/F and the other factor has norm at
most W/F. The norm of its product with any raw Gaussian rational is
therefore bounded by the proved reference-product norm. Both decoded
factor denominators and the reference denominator are retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarRadiusProductBound

open_ipra
open GaussianRationalHorner (positive_product represents)
open GaussianRationalMetric (bounded)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open RationalGaussianEmbedding (native)
open ComplexLogarithmRemainder (normSq mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_product_bound (q r v W F A B : PTm n)
    (hF : Γ ⊢[PRAAx] le one F) (hB : Γ ⊢[PRAAx] le one B)
    (hv : Γ ⊢[PRAAx] represents v (native (ZT.ofNat W)) F)
    (hr : Γ ⊢[PRAAx] bounded r W F)
    (hq : Γ ⊢[PRAAx] bounded (GaussianRationalHorner.qmul q v) A B) : Γ ⊢[PRAAx]
    bounded (GaussianRationalHorner.qmul q r) A B := by
  let D := rawDen q
  let E := rawDen r
  let Q := normSq (rawGaussian q)
  let S := normSq (rawGaussian r)
  have hD := raw_den_positive (Γ := Γ) q
  have hE := raw_den_positive (Γ := Γ) r
  have scalarProduct := GaussianRationalHorner.qmul_represents q v (rawGaussian q) (native (ZT.ofNat W)) D F
    hD hF (raw_represents q) hv
  have old := GaussianRationalMetric.bounded_to_cleared _ _ (D*F) A B
    (positive_product _ _ hD hF) hB scalarProduct hq
  have old' : Γ ⊢[PRAAx] le ((B*B)*(Q*(W*W))) ((A*A)*((D*F)*(D*F))) :=
    le_congr (congrMul (.eqRefl _) (GaussianPositiveScalarProductBound.native_product_norm (rawGaussian q) W)) (.eqRefl _) old
  have radius := GaussianRationalMetric.bounded_to_cleared r (rawGaussian r) E W F hE hF (raw_represents r) hr
  have first := mul_le_mul_right (B*B*Q) radius
  have second := mul_le_mul_right (E*E) old'
  have scaled : Γ ⊢[PRAAx] le ((F*F)*((B*B)*(Q*S))) ((F*F)*((A*A)*((D*E)*(D*E)))) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) first)
      (le_congr (.eqRefl _) (by ipra_ring) second)
  have clear := RationalValueBounds.positive_cancel (positive_product _ _ hF hF) scaled
  exact GaussianRationalMetric.bounded_of_cleared _ _ (D*E) A B (positive_product _ _ hD hE) hB
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ hD hE (raw_represents q) (raw_represents r))
    (le_congr (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_mul _ _)).eqSymm (.eqRefl _) clear)

theorem actual_product_transfers_through_exact_scalar_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 4) ⋏ le one (var 6)) ⟶ represents (var 2) (native (ZT.ofNat (var 3))) (var 4) ⟶
      bounded (var 1) (var 3) (var 4) ⟶ bounded (GaussianRationalHorner.qmul (var 0) (var 2)) (var 5) (var 6) ⟶
      bounded (GaussianRationalHorner.qmul (var 0) (var 1)) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (original_product_bound _ _ _ _ _ _ _ hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianScalarRadiusProductBound
