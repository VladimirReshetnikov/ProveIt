import IPRADerivations.Analysis.GaussianEulerEtaToOneRootGrid
import IPRADerivations.Analysis.GaussianEulerLowerTailRowBound

/-!
# Original Euler rows in the eta-to-one transformed panels

The existing cut offsets and original affine observations are compared
with the new panel's right endpoint. The denominator uses the original
cutoff; the numerator horizon is its root height. No analytic interval
bound is assumed: only the original local sampled modulus is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneRowBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerEtaToOneRootGrid (root rootDen time timeDen totalWidth rightTime right_guard)
open GaussianEulerLowerTailPartition (offset panelWidth root_step_exact exact_panel_width)
open GaussianEulerLowerTailLocalComparison (index index_in_panel panel_gap native_gap native_inside uniform_value)
open GaussianCompactRiemannName (grid sampledModulus value)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaIntegralCutoffs (height)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rootStep (k A R : PTm n) : PTm n := GaussianEulerLowerTailPartition.rootStep zero (height k A R)
def stepScale (k e R : PTm n) : PTm n := succ e*rootStep k (succ e) R
def widthCap (H k e R : PTm n) : PTm n := rootStep k (succ e) R*(succ e*pw (rootDen H k (succ e) R) e)
def rowTime (i j H k A R : PTm n) : PTm n :=
  grid (index i j H zero (height k A R) A) (totalWidth H k A R) (time zero H k A R)
    (totalWidth H k A R) (timeDen H k A R)

theorem uniform_panel_width (i H k e R : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (hi : Γ ⊢[PRAAx] lt i H) : Γ ⊢[PRAAx]
    le (panelWidth i H zero (height k (succ e) R) (succ e)) (widthCap H k e R) := by
  have gap := PowerGap.power_gap (root_step_exact (Γ := Γ) i H zero (height k (succ e) R))
    (right_guard i H k (succ e) R hH hi).andE₂ e
  have ex := natEq (eq_add_of_le (GaussianEulerLowerTailRootGrid.time_monotone (Γ := Γ)
    i (succ i) H zero (height k (succ e) R) (succ e) (le_succ_self i)))
  have cleared : Γ ⊢[PRAAx] le (monus (pw (root (succ i) H k (succ e) R) (succ e))
      (pw (root i H k (succ e) R) (succ e))) (widthCap H k e R) := by
    unfold GaussianEulerLowerTailRootGrid.timeNumerator at ex
    dsimp only [widthCap,rootStep,root]
    ipra_le sl gap using linear_combination ex
  exact le_congr (exact_panel_width i H zero (height k (succ e) R) (succ e)).eqSymm (.eqRefl _) cleared

theorem original_row_distance (F : PR 3) (i j H k e R L x s t : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i H)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i H zero (height k (succ e) R) (succ e)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth H k (succ e) R))
    (hm : Γ ⊢[PRAAx] sampledModulus F (time zero H k (succ e) R)
      (totalWidth H k (succ e) R) (timeDen H k (succ e) R) L x) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F s (rowTime i j H k (succ e) R) x)
      (ap3 F t (rightTime i H k (succ e) R) x)
      (rateNumerator (L*widthCap H k e R) (timeDen H k (succ e) R) s t)
      (rateDenominator (timeDen H k (succ e) R) s t) := by
  let A := succ e
  let a := time zero H k A R
  let b := time (succ i) H k A R
  let W := totalWidth H k A R
  let E := timeDen H k A R
  let u := index i j H zero (height k A R) A
  have ha : Γ ⊢[PRAAx] le one a := le_congr (.eqRefl _)
    (GaussianEulerEtaToOneRootGrid.first_time H k A R).eqSymm (GaussianPolynomialPerturbation.power_positive H A hH)
  have hE : Γ ⊢[PRAAx] le one E := GaussianPolynomialPerturbation.power_positive _ A
    (GaussianEulerEtaToOneRootGrid.denominator_positive H k A R hH)
  have iH : Γ ⊢[PRAAx] le (succ i) H := hi
  have uW : Γ ⊢[PRAAx] le u W := le_trans (index_in_panel i j H zero (height k A R) A hj)
    (GaussianEulerLowerTailPartition.offset_monotone _ _ _ _ _ _ iH)
  have b₁ : Γ ⊢[PRAAx] le a b := GaussianEulerLowerTailRootGrid.time_monotone zero _ _ _ _ _ (zero_le _)
  have b₂ : Γ ⊢[PRAAx] le b (a+W) := le_congr (.eqRefl _)
    (GaussianEulerLowerTailPartition.absolute_offset H H zero (height k A R) A).eqSymm
    (GaussianEulerLowerTailRootGrid.time_monotone _ _ _ _ _ _ iH)
  have pg := panel_gap i j H zero (height k A R) A hj
  have hd := native_gap (a+u) b E (widthCap H k e R) hE pg.andE₁
    (le_trans pg.andE₂ (uniform_panel_width i H k e R hH hi))
  exact GaussianCompactRiemannName.sampled_modulus_at F a W E L x s t _ _ _ _ hm hE
    (GaussianCompactRiemannName.grid_inside u W a W E ha hE hW uW)
    (native_inside a W E b ha hE b₁ b₂)
    (distance_congr (uniform_value u a W E hW hE).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hd)

theorem scale_local_budget (x y s H k e R L : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] distanceBounded x y
      (rateNumerator (L*widthCap H k e R) (timeDen H k (succ e) R) s s)
      (rateDenominator (timeDen H k (succ e) R) s s)) : Γ ⊢[PRAAx]
    distanceBounded x y (L*stepScale k e R*unit s+two*rootDen H k (succ e) R)
      (rootDen H k (succ e) R*unit s) := by
  let D := rootDen H k (succ e) R
  let E := timeDen H k (succ e) R
  let P := unit s
  have hD := GaussianEulerEtaToOneRootGrid.denominator_positive H k (succ e) R hH
  have hE : Γ ⊢[PRAAx] le one E := GaussianPolynomialPerturbation.power_positive D (succ e) hD
  have hP := unit_positive (Γ := Γ) s
  have den : Γ ⊢[PRAAx] le one (rateDenominator E s s) := positive_product _ _ (positive_product _ _ hE hP) hP
  apply distance_radius_mono _ _ _ _ _ _ den (positive_product _ _ hD hP) _ h
  have ep : Γ ⊢[PRAAx] timeDen H k (succ e) R ≐ rootDen H k (succ e) R*pw (rootDen H k (succ e) R) e :=
    GaussianEulerLowerTailRowBound.time_den_product H k e R
  have product := natEq ep
  apply le_of_eq_add (d := zero)
  apply deriveNat
  dsimp only [rateNumerator,rateDenominator,widthCap,stepScale,rootStep,D,E]
  ipra_simps
  rw [product]
  ring

theorem actual_row_norm_bound (i j s H k e z R B L : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hi : Γ ⊢[PRAAx] lt i H)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i H zero (height k (succ e) R) (succ e)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth H k (succ e) R))
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e))
    (hm : Γ ⊢[PRAAx] sampledModulus evaluatorF (time zero H k (succ e) R)
      (totalWidth H k (succ e) R) (timeDen H k (succ e) R) L (fixedData z B)) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (rowTime i j H k (succ e) R) (fixedData z B))
      (GaussianEulerLowerBlockWeight.rowNumerator (rootDen H k (succ e) R) (pw (rootDen H k (succ e) R) e)
        (pw (root (succ i) H k (succ e) R) e) (stepScale k e R) L (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDen H k (succ e) R)
        (pw (root (succ i) H k (succ e) R) e) (unit s)) := by
  let D := rootDen H k (succ e) R
  let U := pw D e
  let V := pw (root (succ i) H k (succ e) R) e
  let S := stepScale k e R
  let P := unit s
  have hD := GaussianEulerEtaToOneRootGrid.denominator_positive H k (succ e) R hH
  have hV := GaussianPolynomialPerturbation.power_positive (Γ := Γ) _ e (right_guard i H k (succ e) R hH hi).andE₁
  have hP := unit_positive (Γ := Γ) s
  have hDP := positive_product _ _ hD hP
  have hVP := positive_product _ _ hV hP
  have near := scale_local_budget _ _ s H k e R L hH (original_row_distance evaluatorF i j H k e R L (fixedData z B) s s hH hi hj hW hm)
  have right := GaussianEulerEtaToOneRootGrid.original_right_observation_bound i s H k z R B (succ e) hH hi h
  have right' := bound_congr (.eqRefl _)
    (congrAdd (congrMul (congrAp2 powF (pred_succ e) (.eqRefl D)) (.eqRefl P)) (congrAp2 powF (pred_succ e) (.eqRefl _)))
    (congrMul (congrAp2 powF (pred_succ e) (.eqRefl _)) (.eqRefl P)) right
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hDP hVP near right'
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hDP hVP)
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) _ raw
  exact le_of_eq_add (d := zero) (by unfold GaussianEulerLowerBlockWeight.rowNumerator GaussianEulerLowerBlockWeight.rowDenominator; dsimp only [D,U,V,S,P]; ipra_ring)

theorem actual_original_eta_to_one_row_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((le one (var 3) ⋏ (lt (var 0) (var 3) ⋏
      (lt (var 1) (panelWidth (var 0) (var 3) zero (height (var 4) (succ (var 5)) (var 7)) (succ (var 5))) ⋏
        (le one (totalWidth (var 3) (var 4) (succ (var 5)) (var 7)) ⋏
          (GaussianEulerLowerPowerCoefficients.source (var 6) (var 7) (var 8) (succ (var 5)) ⋏
            sampledModulus evaluatorF (time zero (var 3) (var 4) (succ (var 5)) (var 7))
              (totalWidth (var 3) (var 4) (succ (var 5)) (var 7)) (timeDen (var 3) (var 4) (succ (var 5)) (var 7)) (var 9) (fixedData (var 6) (var 8))))))) ⟶
      bounded (ap3 evaluatorF (var 2) (rowTime (var 0) (var 1) (var 3) (var 4) (succ (var 5)) (var 7)) (fixedData (var 6) (var 8)))
        (GaussianEulerLowerBlockWeight.rowNumerator (rootDen (var 3) (var 4) (succ (var 5)) (var 7))
          (pw (rootDen (var 3) (var 4) (succ (var 5)) (var 7)) (var 5))
          (pw (root (succ (var 0)) (var 3) (var 4) (succ (var 5)) (var 7)) (var 5)) (stepScale (var 4) (var 5) (var 7)) (var 9) (unit (var 2)))
        (GaussianEulerLowerBlockWeight.rowDenominator (rootDen (var 3) (var 4) (succ (var 5)) (var 7))
          (pw (root (succ (var 0)) (var 3) (var 4) (succ (var 5)) (var 7)) (var 5)) (unit (var 2)))) :=
  closeUniv 11 (.impI (actual_row_norm_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneRowBound
