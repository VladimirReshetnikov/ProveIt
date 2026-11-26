import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerLowerTailPartition
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannSplit

/-!
# Comparing each original lower-grid row to its transformed right endpoint

The cut offsets locate the literal affine-grid observation inside
one transformed panel. The original sampled modulus controls its
distance to that panel's right observation with a uniform numerator
bound from the actual power gap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailLocalComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerTailPartition (rootStep offset panelWidth totalWidth
  offset_monotone absolute_offset uniform_panel_width)
open GaussianEulerLowerTailRootGrid (rootDenominator timeNumerator timeDenominator)
open GaussianCompactRiemannName (inside value grid sampledModulus fraction_congr)
open GaussianCompactRiemannSplit (sharedValue grid_shared_value)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (ofGaussian positive_product ofGaussian_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open ComplexLogarithmRemainder (scale oneCode normSq)
open GaussianRootAlgebra (equal_of_values re_scale im_scale re_sub im_sub re_one im_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def index (i j N p q A : PTm n) : PTm n := offset i N p q A+j
def widthCap (N p q k R : PTm n) : PTm n := rootStep p q*(succ k*pw (rootDenominator N q (succ k) R) k)

theorem index_in_panel (i j N p q A : PTm n) (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q A)) :
    Γ ⊢[PRAAx] le (index i j N p q A) (offset (succ i) N p q A) := by
  have raw := add_le_add₂ (le_refl (Γ := Γ) (offset i N p q A)) (le_of_lt hj)
  exact le_congr (.eqRefl _) (eq_add_of_le (offset_monotone i (succ i) N p q A (le_succ_self i))).eqSymm raw

theorem panel_gap (i j N p q A : PTm n) (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q A)) :
    Γ ⊢[PRAAx]
      le (timeNumerator zero N p q A+index i j N p q A) (timeNumerator (succ i) N p q A) ⋏
      le (monus (timeNumerator (succ i) N p q A) (timeNumerator zero N p q A+index i j N p q A))
        (panelWidth i N p q A) := by
  let start := timeNumerator zero N p q A
  let left := start+index i j N p q A
  let right := timeNumerator (succ i) N p q A
  have h : Γ ⊢[PRAAx] le left right :=
    le_congr (.eqRefl _) (absolute_offset (succ i) N p q A)
      (add_le_add₂ (le_refl start) (index_in_panel i j N p q A hj))
  have e := natEq (eq_add_of_le h)
  have e' := natEq (absolute_offset (Γ := Γ) (succ i) N p q A)
  have e'' := natEq (eq_add_of_le (offset_monotone (Γ := Γ) i (succ i) N p q A (le_succ_self i)))
  refine .andI h ?_
  change Γ ⊢[PRAAx] le (monus right left) (panelWidth i N p q A)
  dsimp only [right,left,start] at e ⊢
  unfold panelWidth index at *
  ipra_le Groth.ι (IPRA.Q.mk Γ j) using linear_combination e+e'-e''

theorem native_value (a E : PTm n) :
    Γ ⊢[PRAAx] value (pairT a E) ≐ ofGaussian (scale a oneCode) E :=
  fraction_congr _ _ _ _ (fst_pair _ _) (snd_pair _ _)

theorem uniform_value (j a C E : PTm n) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] value (grid j C a C E) ≐ value (pairT (a+j) E) := by
  have e : Γ ⊢[PRAAx] C ≐ C*one := by ipra_ring
  have raw := grid_shared_value j one a C E hC hE (le_refl one)
  have normal : Γ ⊢[PRAAx] sharedValue j one a E ≐ ofGaussian (scale (a+j) oneCode) E :=
    fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  have grids := GaussianCompactRiemannName.grid_congr j j C (C*one) a a C C E E
    (.eqRefl _) e (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have code := fraction_congr (fstT (grid j C a C E)) (fstT (grid j (C*one) a C E))
    (sndT (grid j C a C E)) (sndT (grid j (C*one) a C E)) (congrFst grids) (congrSnd grids)
  exact code.eqTrans (raw.eqTrans (normal.eqTrans (native_value _ _).eqSymm))

theorem native_inside (a C E b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E)
    (hlo : Γ ⊢[PRAAx] le a b) (hhi : Γ ⊢[PRAAx] le b (a+C)) :
    Γ ⊢[PRAAx] inside a C E (pairT b E) := by
  let t := pairT b E
  have et : Γ ⊢[PRAAx] fstT t ≐ b := fst_pair _ _
  have dt : Γ ⊢[PRAAx] sndT t ≐ E := snd_pair _ _
  have lo : Γ ⊢[PRAAx] le (a*E) (E*b) :=
    le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right E hlo)
  have hi : Γ ⊢[PRAAx] le (E*b) ((a+C)*E) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right E hhi)
  exact .andI (le_congr (.eqRefl _) et.eqSymm (le_trans ha hlo))
    (.andI (le_congr (.eqRefl _) dt.eqSymm hE)
      (.andI (le_congr (congrMul (.eqRefl _) dt).eqSymm (congrMul (.eqRefl _) et).eqSymm lo)
        (le_congr (congrMul (.eqRefl _) et).eqSymm (congrMul (.eqRefl _) dt).eqSymm hi)))

theorem native_gap (a b E W : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] le a b) (hW : Γ ⊢[PRAAx] le (monus b a) W) :
    Γ ⊢[PRAAx] distanceBounded (value (pairT a E)) (value (pairT b E)) W E := by
  let x := ofGaussian (scale a oneCode) E
  let y := ofGaussian (scale b oneCode) E
  have delta : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (scale b oneCode) (scale a oneCode)) (scale (monus b a) oneCode) := by
    have e := natEq (eq_add_of_le h)
    apply equal_of_values <;> simp only [re_sub,im_sub,re_scale,im_scale,re_one,im_one]
    · ipra_simps
      linear_combination e
    · ring
  have sq : Γ ⊢[PRAAx] normSq (GaussianRootAlgebra.sub (scale b oneCode) (scale a oneCode)) ≐ monus b a*monus b a :=
    (GaussianRootAlgebra.normSq_equal delta).eqTrans
      ((ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
        ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring)))
  have hsq := (GaussianRationalMetric.bounded_difference_iff y x _ _ E W E hE hE
    (ofGaussian_represents _ _ hE) (ofGaussian_represents _ _ hE)).iffMpr
      (le_congr ((mul_comm _ _).eqTrans (congrMul (.eqRefl _) sq).eqSymm)
        (.eqRefl _) (mul_le_mul_right (E*E) (sq_le_sq hW)))
  exact distance_congr (native_value _ _).eqSymm (native_value _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ hE hsq)

def rightTime (i N p q A R : PTm n) : PTm n :=
  pairT (timeNumerator (succ i) N p q A) (timeDenominator N q A R)
def rowTime (i j N p q A R : PTm n) : PTm n :=
  grid (index i j N p q A) (totalWidth N p q A) (timeNumerator zero N p q A)
    (totalWidth N p q A) (timeDenominator N q A R)

theorem original_row_distance (F : PR 3) (i j N p q k R L x s t : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N)
    (hj : Γ ⊢[PRAAx] lt j (panelWidth i N p q (succ k)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth N p q (succ k)))
    (hm : Γ ⊢[PRAAx] sampledModulus F (timeNumerator zero N p q (succ k))
      (totalWidth N p q (succ k)) (timeDenominator N q (succ k) R) L x) :
    Γ ⊢[PRAAx] distanceBounded
      (ap3 F s (rowTime i j N p q (succ k) R) x) (ap3 F t (rightTime i N p q (succ k) R) x)
      (rateNumerator (L*widthCap N p q k R) (timeDenominator N q (succ k) R) s t)
      (rateDenominator (timeDenominator N q (succ k) R) s t) := by
  let A := succ k
  let a := timeNumerator zero N p q A
  let b := timeNumerator (succ i) N p q A
  let W := totalWidth N p q A
  let E := timeDenominator N q A R
  let u := index i j N p q A
  have ha : Γ ⊢[PRAAx] le one a :=
    le_congr (.eqRefl _) (GaussianEulerLowerTailRootGrid.time_first N p q A).eqSymm
      (GaussianPolynomialPerturbation.power_positive N A hN)
  have hE : Γ ⊢[PRAAx] le one E :=
    GaussianPolynomialPerturbation.power_positive _ A (positive_product _ _ (unit_positive _) hN)
  have iN : Γ ⊢[PRAAx] le (succ i) N := hi
  have uW : Γ ⊢[PRAAx] le u W := le_trans (index_in_panel i j N p q A hj) (offset_monotone _ _ _ _ _ _ iN)
  have b₁ : Γ ⊢[PRAAx] le a b :=
    GaussianEulerLowerTailRootGrid.time_monotone zero _ _ _ _ _ (zero_le _)
  have b₂ : Γ ⊢[PRAAx] le b (a+W) :=
    le_congr (.eqRefl _) (absolute_offset N N p q A).eqSymm
      (GaussianEulerLowerTailRootGrid.time_monotone _ _ _ _ _ _ iN)
  have hgap := panel_gap i j N p q A hj
  have hd := native_gap (a+u) b E (widthCap N p q k R) hE hgap.andE₁
    (le_trans hgap.andE₂ (uniform_panel_width i N p q k R hN hpq hi))
  exact GaussianCompactRiemannName.sampled_modulus_at F a W E L x s t _ _ _ _ hm hE
    (GaussianCompactRiemannName.grid_inside u W a W E ha hE hW uW) (native_inside a W E b ha hE b₁ b₂)
    (distance_congr (uniform_value u a W E hW hE).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hd)

theorem actual_lower_row_modulus_comparison_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (((le one (var 2) ⋏ le (var 3) (var 4)) ⋏ lt (var 0) (var 2)) ⟶
        (lt (var 1) (panelWidth (var 0) (var 2) (var 3) (var 4) (succ (var 5))) ⋏
          le one (totalWidth (var 2) (var 3) (var 4) (succ (var 5)))) ⟶
        sampledModulus F (timeNumerator zero (var 2) (var 3) (var 4) (succ (var 5)))
          (totalWidth (var 2) (var 3) (var 4) (succ (var 5)))
          (timeDenominator (var 2) (var 4) (succ (var 5)) (var 6)) (var 7) (var 8) ⟶
        distanceBounded
          (ap3 F (var 9) (rowTime (var 0) (var 1) (var 2) (var 3) (var 4) (succ (var 5)) (var 6)) (var 8))
          (ap3 F (var 10) (rightTime (var 0) (var 2) (var 3) (var 4) (succ (var 5)) (var 6)) (var 8))
          (rateNumerator ((var 7)*widthCap (var 2) (var 3) (var 4) (var 5) (var 6))
            (timeDenominator (var 2) (var 4) (succ (var 5)) (var 6)) (var 9) (var 10))
          (rateDenominator (timeDenominator (var 2) (var 4) (succ (var 5)) (var 6)) (var 9) (var 10))) :=
  closeUniv 11 (.impI (.impI (.impI (original_row_distance F _ _ _ _ _ _ _ _ _ _ _
    hyp2.andE₁.andE₁ hyp2.andE₁.andE₂ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailLocalComparison
