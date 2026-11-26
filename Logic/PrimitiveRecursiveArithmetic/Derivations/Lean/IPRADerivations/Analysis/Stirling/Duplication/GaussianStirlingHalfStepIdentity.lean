import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingHalfStepAlgebra
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationConstant
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationResidual
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRecurrence
import IPRADerivations.Analysis.Stirling.Wallis.GaussianStirlingWallisLogIdentity

/-!
# Named Stirling half-step identity

The observed difference A(n+1/2) − A(n) equals half the logarithm
of the original Wallis ratio, plus the signed duplication residual.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingHalfStepIdentity

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast sum_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (three add_sample_error multiply_sample_error product_right_error through_identity)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianStirlingDifferenceAlgebra (rawA)
open GaussianStirlingDuplicationAlgebra (rawResidual)
open GaussianStirlingDuplicationLogs (halfRatioData)
open GaussianStirlingHalfStepAlgebra (rawHalfGamma half_step_value)
open GaussianStirlingNames (source point nameF nameData name_regular logGammaF logGammaData log_gamma_regular
  logXF logXData log_x_regular)
open GaussianStirlingRecurrence (scaleBudget aBudget a_error)
open GaussianStirlingWallisGammaRatio (halfNumerator half_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => logGammaF
local notation "X" => logXF
local notation "H" => GaussianStirlingWallisLogRate.nameF
local notation "W" => GaussianPositiveRationalLogarithm.logF
local notation "R" => GaussianStirlingDuplicationResidual.nameF
local notation "I" => GaussianStirlingWallisLogIdentity.rightF
local notation "idData" => GaussianStirlingWallisLogIdentity.rightData
local notation "wallData" => GaussianStirlingWallisLogRate.data
local notation "residualData" => GaussianStirlingDuplicationResidual.nameData
local notation "c" => point one two

def differenceF : PR 2 := GaussianNamedDifference.nameF nameF nameF
def differenceData (r : PTm n) : PTm n :=
  GaussianNamedDifference.data (nameData (halfNumerator r) two) (nameData (succ r) one)
def scaledLogF : PR 2 := multiplyF constantF H
def scaledLogData (r x : PTm n) : PTm n := multiplyData constantF H c (wallData r x)
def rightF : PR 2 := addF scaledLogF R
def rightData (r x : PTm n) : PTm n := addData (scaledLogData r x) (residualData (succ r) one)

ipra_subst differenceData [two, one]
ipra_subst scaledLogData [two, one]
ipra_subst rightData [GaussianStirlingDuplicationResidual.nameData, GaussianStirlingDuplicationResidual.productData, halfRatioData, GaussianStirlingNativeDuplication.halfNumerator, one, two]

theorem integer_source (r : PTm n) : Γ ⊢[PRAAx] source (succ r) one :=
  .andI (zero_lt_succ r) (le_refl one)

theorem scaled_log_regular (r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] pointCN scaledLogF (scaledLogData r x) :=
  multiply_fast constantF H c (wallData r x) (constant_regular _) (GaussianStirlingWallisLogRate.name_regular r x hn)

private theorem sum_near (f g : PR 2) (p x y u v A B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hu : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) u A (unit p))
    (hv : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) v B (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF f g) p (addData x y)) (qadd u v) (three+(A+B)) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (add_sample_error _ _ _ _ p hf hg)
    (sum_distance _ _ _ _ _ _ _ (unit_positive p) hu hv)

private theorem multiply_near (f : PR 2) (p d x v A : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hv : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) v A (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF constantF f) p (multiplyData constantF f d x)) (qmul d v)
      (scaleBudget f d x A) (unit p) := by
  have hc := constant_regular (Γ := Γ) d
  have first := multiply_sample_error constantF f d x p hc hf
  have read := constant_at (Γ := Γ) p d
  have bound := GaussianRationalReciprocal.bound_congr read (.eqRefl _) (.eqRefl _) (sample_bound constantF d p hc)
  have last := product_right_error d _ v A (unit p) (U f x) (U constantF d) (unit_positive p) hv
    (sample_bound f x p hf) bound
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr read (.eqRefl _)) (.eqRefl _) (.eqRefl _) first) last

private theorem half_gamma_cross (r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] crossEquivalent L (multiplyF constantF I) (logGammaData (halfNumerator r) two)
      (multiplyData constantF I c (idData r x)) := by
  let D := GaussianStirlingWallisLogIdentity.doubleLogF
  let g := logGammaData (halfNumerator r) two
  let i := GaussianStirlingWallisLogIdentity.leftData r
  let j := idData r x
  have h := log_gamma_regular _ _ (half_source (Γ := Γ) r)
  have g₀ := log_gamma_regular _ _ (integer_source (Γ := Γ) r)
  have l₀ := log_x_regular _ _ (integer_source (Γ := Γ) r)
  have hW := GaussianStirlingWallisLogRate.name_regular r x hn
  have hI : Γ ⊢[PRAAx] pointCN I j :=
    add_fast _ _ _ _ hW (add_fast _ _ _ _ l₀ (add_fast _ _ _ _ g₀ g₀))
  have hc := constant_regular (Γ := Γ) (c : PTm n)
  have step := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF D I c c i j hc hc
    (add_fast L L g g h h) hI (cross_refl _ _ hc)
    (GaussianStirlingWallisLogIdentity.logarithmic_identity r x hn)
  exact cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (GaussianStirlingDuplicationConstant.scale_half_double L g h)) step

def nestedBudget : PTm n := three+(zero+(three+(zero+(three+(zero+zero)))))
def halfGammaBudget (r x : PTm n) : PTm n := two+scaleBudget I c (idData r x) nestedBudget

private theorem half_gamma_near (p r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 L p (logGammaData (halfNumerator r) two))
      (rawHalfGamma (ap2 L p (logGammaData (succ r) one)) (ap2 X p (logXData (succ r) one))
        (ap2 H p (wallData r x))) (halfGammaBudget r x) (unit p) := by
  let g := logGammaData (succ r) one
  let l := logXData (succ r) one
  let h := wallData r x
  let d := addData g g
  let j := addData l d
  let D := addF L L
  let J := addF X D
  have regularG := log_gamma_regular _ _ (integer_source (Γ := Γ) r)
  have regularL := log_x_regular _ _ (integer_source (Γ := Γ) r)
  have regularH := GaussianStirlingWallisLogRate.name_regular r x hn
  have regularD := add_fast _ _ _ _ regularG regularG
  have regularJ := add_fast _ _ _ _ regularL regularD
  have regularI : Γ ⊢[PRAAx] pointCN I (idData r x) := add_fast _ _ _ _ regularH regularJ
  have bp := unit_positive (Γ := Γ) p
  have zG := distance_refl_zero (ap2 L p g) _ bp
  have zL := distance_refl_zero (ap2 X p l) _ bp
  have zH := distance_refl_zero (ap2 H p h) _ bp
  have eD := sum_near L L p g g _ _ zero zero regularG regularG zG zG
  have eJ := sum_near X D p l d _ _ zero (three+(zero+zero)) regularL regularD zL eD
  have eI := sum_near H J p h j _ _ zero (three+(zero+(three+(zero+zero)))) regularH regularJ zH eJ
  have m := multiply_near I p c (idData r x) _ nestedBudget regularI eI
  have e := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (half_gamma_cross r x hn))
  exact distance_triangle_same _ _ _ _ _ _ bp e m

private theorem half_log_cross (r : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent X (addF X W) (logXData (halfNumerator r) two)
      (addData (logXData (succ r) one) (halfRatioData (succ r) one)) := by
  have e : Γ ⊢[PRAAx] logXData (halfNumerator r) (one*two) ≐ logXData (halfNumerator r) two := by
    simpa using Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (logXData (var 0) (var 1) : PTm 2)
      (σ := ![halfNumerator r,one*two]) (σ' := ![halfNumerator r,two])
      (fun i => by fin_cases i; exact .eqRefl _; exact one_mul _)
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ e (.eqRefl _)
    (GaussianStirlingDuplicationLogs.half_log (succ r) one (integer_source r))

def residualBudget (r : PTm n) : PTm n := num 6+(zero+scaleBudget W (point (succ r) one) (halfRatioData (succ r) one) zero)

private theorem residual_near (p r : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 R p (residualData (succ r) one))
      (rawResidual (succ r) one (ap2 W p (halfRatioData (succ r) one))) (residualBudget r) (unit p) := by
  let a := succ r
  let x := halfRatioData a one
  let z := point a one
  have bp := unit_positive (Γ := Γ) p
  have hW := GaussianStirlingDuplicationResidual.log_regular (Γ := Γ) a one (zero_lt_succ r)
  have hc := constant_regular (Γ := Γ) (c : PTm n)
  have hZ := constant_regular (Γ := Γ) z
  have prod := multiply_near W p z x (ap2 W p x) zero hW (distance_refl_zero _ _ bp)
  have first := GaussianNamedDifference.sample_error constantF (multiplyF constantF W) c (multiplyData constantF W z x)
    p hc (multiply_fast _ _ _ _ hZ hW)
  have left := distance_congr (constant_at (Γ := Γ) p c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero c _ bp)
  exact distance_triangle_same _ _ _ _ _ _ bp first (difference_distance _ _ _ _ _ _ _ bp left prod)

def errorBudget (r x : PTm n) : PTm n :=
  (num 6+(aBudget (halfNumerator r) two (halfGammaBudget r x) (two+three)+aBudget (succ r) one zero zero))+
    (three+(scaleBudget H c (wallData r x) zero+residualBudget r))

set_option maxHeartbeats 2600000 in
theorem identity_error (p r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData r)) (ap2 rightF p (rightData r x))
      (errorBudget r x) (unit p) := by
  let a := succ r
  let b := halfNumerator r
  let g := ap2 L p (logGammaData a one)
  let l := ap2 X p (logXData a one)
  let w := ap2 W p (halfRatioData a one)
  let h := ap2 H p (wallData r x)
  have bp := unit_positive (Γ := Γ) p
  have hs := integer_source (Γ := Γ) r
  have hh := half_source (Γ := Γ) r
  have hW := GaussianStirlingDuplicationResidual.log_regular a one hs.andE₁
  have lh := log_x_regular a one hs
  have split := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (half_log_cross (Γ := Γ) r))
  have halfLog := distance_triangle_same _ _ _ _ _ _ bp split
    (add_sample_error X W (logXData a one) (halfRatioData a one) p lh hW)
  have e0 := a_error p a one g l zero zero hs (distance_refl_zero _ _ bp) (distance_refl_zero _ _ bp)
  have eH := a_error p b two (rawHalfGamma g l h) (qadd l w) (halfGammaBudget r x) (two+three) hh
    (half_gamma_near p r x hn) halfLog
  have raw := GaussianNamedDifference.sample_error nameF nameF (nameData b two) (nameData a one) p
    (name_regular b two hh) (name_regular a one hs)
  have left := distance_triangle_same _ _ _ _ _ _ bp raw (difference_distance _ _ _ _ _ _ _ bp eH e0)
  have rh := GaussianStirlingWallisLogRate.name_regular r x hn
  have rR := GaussianStirlingDuplicationResidual.name_regular a one hs
  have right := sum_near scaledLogF R p (scaledLogData r x) (residualData a one) (qmul c h) (rawResidual a one w)
    (scaleBudget H c (wallData r x) zero) (residualBudget r) (scaled_log_regular r x hn) rR
    (multiply_near H p c (wallData r x) h zero rh (distance_refl_zero _ _ bp)) (residual_near p r)
  exact through_identity _ _ _ _ _ _ _ bp left right (half_step_value a g l w h)

private theorem subst_errorBudget {m : ℕ} (σ : Fin n → PTm m) (r x : PTm n) :
    Syn.subst σ (errorBudget r x) = errorBudget (Syn.subst σ r) (Syn.subst σ x) := by
  simp [errorBudget,aBudget,halfGammaBudget,scaleBudget,residualBudget,nestedBudget,three,halfRatioData,
    GaussianStirlingNativeDuplication.halfNumerator,one,two]

theorem half_step_identity (r x : PTm n) (hn : Γ ⊢[PRAAx] le (num 6) (succ r)) :
    Γ ⊢[PRAAx] crossEquivalent differenceF rightF (differenceData r) (rightData r x) := by
  have h := integer_source (Γ := Γ) r
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (errorBudget r x)
    (GaussianNamedDifference.name_regular nameF nameF _ _
      (name_regular _ _ (half_source r)) (name_regular _ _ h))
    (add_fast _ _ _ _ (scaled_log_regular r x hn) (GaussianStirlingDuplicationResidual.name_regular _ _ h)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (num 6) (succ (Syn.shift r)) := by
    simpa [Fm.shift,Syn.shift] using hn.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_errorBudget,subst_differenceData,subst_rightData]
    using identity_error (var 0) (Syn.shift r) (Syn.shift x) hs

theorem actual_stirling_half_step_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 6) (succ (var 0)) ⟶ crossEquivalent differenceF rightF (differenceData (var 0)) (rightData (var 0) (var 1))) :=
  closeUniv 2 (.impI (half_step_identity _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingHalfStepIdentity
