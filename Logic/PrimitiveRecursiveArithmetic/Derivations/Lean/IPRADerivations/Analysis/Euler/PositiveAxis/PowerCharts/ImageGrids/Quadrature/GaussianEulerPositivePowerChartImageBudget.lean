import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.Quadrature.GaussianEulerPositivePowerChartImageName

/-!
# Dyadic error budgets for the exact corrected image integral

Four finite inequalities control the true Lipschitz mesh error, the
tilt error and the two independent Euler observation errors. This is a
comparison to an ordinary compact Euler observation at the exact
rational endpoints of the corrected panel.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageBudget

open_ipra
open GaussianEulerPositivePowerChartImageCuts (data count)
open GaussianEulerPositivePowerChartImageComparison (ordinary)
open GaussianEulerPositivePowerChartImageName (panelTop panelModulus latticeFactor observation)
open GaussianEulerPositivePowerChartImageRows (cost errorDenominator)
open GaussianEulerPositivePowerChartImage (query)
open GaussianEulerPositivePowerChart (lipschitz)
open GaussianEulerPositivePowerChartMesh (widthNumerator cellDenominator)
open GaussianEulerPowerScalingCorrectedQuadrature (source correctedSum)
open GaussianCompactRiemannName (precision)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same distance_congr distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def meshBudget (R h Q S E T C : PTm n) : PTm n :=
  num 4*panelTop Q S E T*panelModulus R h Q S E T*lipschitz Q S E T*C
def tiltBudget (R h Q S E T : PTm n) : PTm n :=
  num 16*panelTop Q S E T*panelModulus R h Q S E T
def observationBudget (Q S E T : PTm n) : PTm n := num 4*panelTop Q S E T
def rowBudget (s p q k R h Q S E T C N : PTm n) : Fm PTm n :=
  le (meshBudget R h Q S E T C*unit s) N ⋏
    (le (tiltBudget R h Q S E T*unit s) (unit (query k h Q E T)) ⋏
      (le (observationBudget Q S E T*unit s) (unit p) ⋏
        le (observationBudget Q S E T*unit s) (unit q)))

theorem row_budget_inequality (s p q k R h Q S E T C N : PTm n)
    (hE : Γ ⊢[PRAAx] le one E)
    (hs : Γ ⊢[PRAAx] rowBudget s p q k R h Q S E T C N) :
    Γ ⊢[PRAAx] le (panelTop Q S E T*cost p q k R h Q S E T C N*unit s)
      (errorDenominator p q k h Q E T N) := by
  let W := lipschitz Q S E T
  let L := panelModulus R h Q S E T
  let U := panelTop Q S E T
  let F := unit (query k h Q E T)
  let V := unit s
  let P := unit p
  let Q' := unit q
  let A := E*N
  let D := A*F*Q'*P
  have nle : Γ ⊢[PRAAx] le N A := le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N hE)
  have h1 : Γ ⊢[PRAAx] le (num 4*(U*L*W*C*F*Q'*P*V)) D := by
    have m := mul_le_mul_right (F*Q'*P) (le_trans hs.andE₁ nle)
    exact le_congr (by unfold meshBudget; dsimp only [L,U,W,V]; ipra_ring) (by dsimp only [D]; ipra_ring) m
  have h2 : Γ ⊢[PRAAx] le (num 4*(num 4*U*L*A*Q'*P*V)) D := by
    have m := mul_le_mul_right (A*Q'*P) hs.andE₂.andE₁
    exact le_congr (by unfold tiltBudget; dsimp only [L,U,V]; ipra_ring) (by dsimp only [D]; ipra_ring) m
  have h3 : Γ ⊢[PRAAx] le (num 4*(U*A*F*Q'*V)) D := by
    have m := mul_le_mul_right (A*F*Q') hs.andE₂.andE₂.andE₁
    exact le_congr (by unfold observationBudget; dsimp only [U,V]; ipra_ring)
      (by dsimp only [D]; ipra_ring) m
  have h4 : Γ ⊢[PRAAx] le (num 4*(U*A*F*P*V)) D := by
    have m := mul_le_mul_right (A*F*P) hs.andE₂.andE₂.andE₂
    exact le_congr (by unfold observationBudget; dsimp only [U,V]; ipra_ring)
      (by dsimp only [D]; ipra_ring) m
  apply RationalValueBounds.positive_cancel (c := num 4) (le_of_eq_add (d := num 3) (by ipra_ring))
  have all := add_le_add₂ (add_le_add₂ h1 h2) (add_le_add₂ h3 h4)
  exact le_congr
    (by unfold cost GaussianNamedInverseRate.rateNumerator widthNumerator cellDenominator
          GaussianEulerPositivePowerChartMesh.timeDenominator
        dsimp only [U,L,W,A,F,Q',P,V]
        unfold panelModulus panelTop
        ipra_ring)
    (by unfold errorDenominator GaussianNamedInverseRate.rateDenominator cellDenominator
          GaussianEulerPositivePowerChartMesh.timeDenominator
        dsimp only [D,A,F,Q',P]
        ipra_ring) all

theorem original_dyadic_named_quadrature (s p q k z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N)
    (hq : Γ ⊢[PRAAx] le (precision s (panelTop Q S E T)) q)
    (hb : Γ ⊢[PRAAx] rowBudget s p q k R h Q S E T C N) : Γ ⊢[PRAAx]
    distanceBounded (observation s k z R B e f d h Q S E T a C N)
      (correctedSum p k z B e f d h Q S E T a C N) two (unit s) := by
  let J := latticeFactor s R h Q S E T
  have hJ : Γ ⊢[PRAAx] le one J := GaussianCompactRiemannName.mesh_positive _ _ _
  have hU := unit_positive (Γ := Γ) s
  have hV := unit_positive (Γ := Γ) (s+num 6)
  have hc := GaussianEulerPositivePowerChartImageName.original_lattice_to_compact_name s q k z R B e f d h Q S E T a C N hs hq
  have hL := distance_radius_mono _ _ _ _ one (unit s) hV hU
    (le_congr (.eqRefl _) (by ipra_ring) (GaussianCompactRiemannName.dyadic_six_lower s)) hc
  have current := GaussianEulerPositivePowerChartImageComparison.original_lattice_comparison p q k z R B e f d h Q S E T a C N J hs hJ
  have hE := hs.andE₂.andE₁.andE₂.andE₁
  have hp := GaussianEulerPositivePowerChartImageRows.cell_denominator_positive k e f d h Q S E T a C N hs.andE₂
  have hd : Γ ⊢[PRAAx] le one (errorDenominator p q k h Q E T N) :=
    positive_product _ _ (positive_product _ _ hp (unit_positive q)) (unit_positive p)
  have closer := distance_radius_mono _ _ _ _ one (unit s) hd hU
    (le_congr (.eqRefl _) (by ipra_ring) (row_budget_inequality s p q k R h Q S E T C N hE hb)) current
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ one one _ hU (distance_symmetric _ _ _ _ hU hL) closer)

theorem actual_original_corrected_image_named_dyadic_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)
      (var 13) (var 14) (var 15) (var 16) (var 17) ⋏
      (le (precision (var 0) (panelTop (var 11) (var 12) (var 13) (var 14))) (var 2) ⋏
        rowBudget (var 0) (var 1) (var 2) (var 3) (var 5) (var 10) (var 11) (var 12) (var 13) (var 14) (var 16) (var 17))) ⟶
      distanceBounded (observation (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) (var 16) (var 17))
        (correctedSum (var 1) (var 3) (var 4) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
          (var 12) (var 13) (var 14) (var 15) (var 16) (var 17)) two (unit (var 0))) :=
  closeUniv 18 (.impI (original_dyadic_named_quadrature _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImageBudget
