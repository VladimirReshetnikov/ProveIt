import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalPositiveLogarithmRecurrence
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedSumDifference
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceAlgebra
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifferenceZero
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness

/-!
# The real logarithmic quotient in the Barnes characterization

Take the actual logarithm of the positive candidate data. A checked
recurrence of the candidate with the original Gamma evaluator gives the
same real Log Gamma increment as for the canonical Barnes logarithm.
Their difference is then invariant under the unit shift.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasLogQuotient

open_ipra
open GaussianBarnesCanonicalHyperfactorial (logarithm_source specialLogData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianRealNameExponentialInjectivity (axisSamples difference_real_samples independent_radii_injective)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "Log" => GaussianNamedPositiveLogarithm.nameF
local notation "logd" => GaussianNamedPositiveLogarithm.data
local notation "K" => GaussianLogGammaEulerCofinal.nameF
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "gd" => GaussianStirlingGammaLogarithm.gammaData
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

abbrev nameF (f : PR 2) : PR 2 := Diff (Log f) L
def data (a b x P : PTm n) : PTm n := dd (logd x P) (ld a b (a+b))

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b x P : PTm n) :
    Syn.subst σ (data a b x P) = data (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) (Syn.subst σ P) := by
  simp [data]

def source (f : PR 2) (a b x y P T Q W : PTm n) : Fm PTm n :=
  (le one a ⋏ le one b) ⋏
    ((GaussianNamedPositiveLogarithm.source f x P T ⋏ GaussianNamedPositiveLogarithm.source f y Q W) ⋏
      crossEquivalent (multiplyF f G) f (multiplyData f G x (gd a b)) y)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (a b x y P T Q W : PTm n) :
    (source f a b x y P T Q W).subst σ = source f (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ P) (Syn.subst σ T) (Syn.subst σ Q) (Syn.subst σ W) := by
  simp [source,one,GaussianStirlingGammaLogarithm.gammaData]

theorem regular (f : PR 2) (a b x P T : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T) : Γ ⊢[PRAAx] pointCN (nameF f) (data a b x P) :=
  GaussianNamedDifference.name_regular _ _ _ _ (GaussianNamedPositiveLogarithm.name_regular f x P T hx)
    (GaussianBarnesCanonicalPositiveLogarithm.regular a b _ (GaussianBarnesCanonicalPositiveLogarithm.default_source a b ha hb))

theorem axis_samples (f : PR 2) (a b x P : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] axisSamples (nameF f) (data a b x P) :=
  GaussianBarnesCanonicalPositiveLogarithmRealAxis.real_axis _ _
    (difference_real_samples _ _ _ _ (GaussianNamedPositiveLogarithm.real_samples f x P)
      (GaussianBarnesCanonicalPositiveLogarithmRealAxis.samples_axis a b _
        (GaussianBarnesCanonicalPositiveLogarithm.default_source a b ha hb)))

theorem log_shift (f : PR 2) (a b x y P T Q W : PTm n) (hs : Γ ⊢[PRAAx] source f a b x y P T Q W) :
    Γ ⊢[PRAAx] crossEquivalent (Log f) (addF (Log f) K) (logd y Q) (addData (logd x P) (specialLogData a b)) := by
  let F := Log f
  let X := logd x P
  let Y := logd y Q
  let k := specialLogData a b
  let Z := addF F K
  let z := addData X k
  let R := GaussianCompactLogarithmBounds.radius P T
  let S := GaussianLogGammaEulerExponentialLimit.disk a zero b zero
  let D := GaussianCompactLogarithmBounds.radius Q W
  have hx := hs.andE₂.andE₁.andE₁
  have hy := hs.andE₂.andE₁.andE₂
  have hk := logarithm_source a b hs.andE₁.andE₁ hs.andE₁.andE₂
  have qx := GaussianNamedPositiveLogarithm.name_regular f x P T hx
  have qk := GaussianLogGammaEulerCofinal.canonical_regular a zero b zero hk
  have qz := add_fast F K X k qx qk
  have ix := GaussianNamedPositiveLogarithm.exponential_input f x P T hx
  have iy := GaussianNamedPositiveLogarithm.exponential_input f y Q W hy
  have ik := GaussianExponentialRadiusIndependence.input_widen K (U K k) S k (exponential_input _ _ qk) (le_add_right _ _)
  have iz := exponential_input Z z qz
  have factors := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent F K Z
    R S (U Z z) X k z ix ik iz (cross_refl _ _ qz)
  have product := GaussianGammaAdjacentCutoff.multiply_cross (E F) f (E K) G (ed R X) x (ed S k) (gd a b)
    (GaussianRadiusExponentialName.name_regular _ _ _ ix) hx.andE₁
    (GaussianRadiusExponentialName.name_regular _ _ _ ik) (GaussianStirlingGammaLogarithm.gamma_regular a b hs.andE₁)
    (GaussianNamedPositiveLogarithmExponential.original_recovery f x P T hx)
    (GaussianLogGammaEulerPositiveAxis.axis_exponential_gamma a b zero hk)
  exact independent_radii_injective F Z D (U Z z) Y z iy iz (GaussianNamedPositiveLogarithm.real_samples f y Q)
    (GaussianNamedPositiveLogarithmScale.sum_axis F K X k (GaussianNamedPositiveLogarithm.real_samples f x P)
      (GaussianLogGammaEulerPositiveAxis.cofinal_axis_samples a b zero hk))
    (cross_trans _ _ _ _ _ _ (GaussianNamedPositiveLogarithmExponential.original_recovery f y Q W hy)
      (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ hs.andE₂.andE₂)
        (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ product) factors)))

private theorem shift_difference (F H : PR 2) (x y h : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hy : Γ ⊢[PRAAx] pointCN F y) (hh : Γ ⊢[PRAAx] pointCN H h)
    (e : Γ ⊢[PRAAx] crossEquivalent F (addF F H) y (addData x h)) :
    Γ ⊢[PRAAx] crossEquivalent (Diff F F) H (dd y x) h :=
  cross_trans _ _ _ _ _ _
    (difference_proper F (addF F H) F F y (addData x h) x x hy (add_fast _ _ _ _ hx hh) hx hx e (cross_refl _ _ hx))
    (GaussianNamedSumDifference.cancel_added F H x h hx hh)

theorem unit_period (f : PR 2) (a b x y P T Q W : PTm n) (hs : Γ ⊢[PRAAx] source f a b x y P T Q W) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data (a+b) b y Q) (data a b x P) := by
  let F := Log f
  let X := logd x P
  let Y := logd y Q
  let l := ld a b (a+b)
  let m := ld (a+b) b ((a+b)+b)
  let k := specialLogData a b
  have ha := hs.andE₁.andE₁
  have hb := hs.andE₁.andE₂
  have hc := le_trans ha (le_add_right a b)
  have fx := GaussianNamedPositiveLogarithm.name_regular f x P T hs.andE₂.andE₁.andE₁
  have fy := GaussianNamedPositiveLogarithm.name_regular f y Q W hs.andE₂.andE₁.andE₂
  have hl := GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ (GaussianBarnesCanonicalPositiveLogarithm.default_source a b ha hb)
  have hm := GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ (GaussianBarnesCanonicalPositiveLogarithm.default_source (a+b) b hc hb)
  have hk := GaussianBarnesCanonicalHyperfactorialPowerStep.logarithm_regular a b ha hb
  have lhs := shift_difference F K X Y k fx fy hk (log_shift f a b x y P T Q W hs)
  have rhs := shift_difference L K l m k hl hm hk (GaussianBarnesCanonicalPositiveLogarithmRecurrence.recurrence a b ha hb)
  have moved := difference_proper (Diff F F) K (Diff L L) K (dd Y X) k (dd m l) k
    (GaussianNamedDifference.name_regular _ _ _ _ fy fx) hk (GaussianNamedDifference.name_regular _ _ _ _ hm hl) hk lhs rhs
  have zero := GaussianNamedDifferenceZero.difference_zero K K k k (zero : PTm n) hk hk (cross_refl _ _ hk)
  exact GaussianNamedDifferenceZero.cross_of_zero _ _ _ _ _
    (GaussianNamedDifference.name_regular _ _ _ _ fy hm) (GaussianNamedDifference.name_regular _ _ _ _ fx hl)
    (cross_trans _ _ _ _ _ _ (GaussianNamedDifferenceAlgebra.shuffle F L F L Y m X l fy hm fx hl)
      (cross_trans _ _ _ _ _ _ moved zero))

theorem actual_Barnes_candidate_log_quotient_unit_period_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let a := var 0
     let b := var 1
     let x := var 2
     let y := var 3
     let P := var 4
     let T := var 5
     let Q := var 6
     let W := var 7
     source f a b x y P T Q W ⟶ crossEquivalent (nameF f) (nameF f) (data (a+b) b y Q) (data a b x P)) :=
  closeUniv 8 (.impI (unit_period f _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasLogQuotient
