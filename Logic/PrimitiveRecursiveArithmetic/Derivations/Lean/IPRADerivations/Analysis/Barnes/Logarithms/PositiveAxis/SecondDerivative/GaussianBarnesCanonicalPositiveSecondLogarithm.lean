import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmRows
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactor
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.SecondDerivative.GaussianBarnesCanonicalSecondDerivativeCofinal
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# The original positive Barnes logarithm's second-derivative expression

Combine the original prefactor coefficient −(1+γ), the exact finite kept
second-derivative rows, and the cofinal sampler of the original retained
rows. Arbitrary late finite prefixes approximate the actual name while
retaining the literal prefactor sample at the requested clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondLogarithm

open_ipra
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactor (quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_sample_error_right three)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianBarnesCanonicalSecondDerivativeCofinal.nameF
local notation "sd" => GaussianBarnesCanonicalLogCofinal.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "v" => GaussianBarnesCanonicalSecondDerivativeTail.value

def coefficientF : PR 2 := negativeF quadraticCoefficientF

def coefficientData : PTm n := negativeData quadraticCoefficientData

def seriesF : PR 2 := addF constantF S

def seriesData (A B R : PTm n) : PTm n := addData (v (center A B) B zero (initial R)) (sd (center A B) R B)

def nameF : PR 2 := addF coefficientF seriesF

def data (A B R : PTm n) : PTm n := addData coefficientData (seriesData A B R)

def prefixValue (A B R r : PTm n) : PTm n := v (center A B) B zero (initial R+r)

@[simp] theorem subst_coefficientData {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (coefficientData : PTm n) = (coefficientData : PTm m) := by
  simp [coefficientData,quadraticCoefficientData]

@[simp] theorem subst_seriesData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (seriesData A B R) = seriesData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [seriesData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (data A B R) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [data]

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (A B R r : PTm n) :
    Syn.subst σ (prefixValue A B R r) = prefixValue (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ r) :=
  by simp [prefixValue]

theorem coefficient_regular : Γ ⊢[PRAAx] pointCN coefficientF (coefficientData : PTm n) :=
  negative_fast _ _ quadratic_coefficient_regular

theorem series_regular (A B R : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] pointCN seriesF (seriesData A B R) :=
  add_fast _ _ _ _ (constant_regular _) (GaussianBarnesCanonicalSecondDerivativeCofinal.regular _ _ _ h)

theorem regular (A B R : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B R) :=
  add_fast _ _ _ _ coefficient_regular (series_regular A B R h)

theorem prefix_split (A B R r : PTm n) :
    Γ ⊢[PRAAx] prefixValue A B R r ≐ qadd (v (center A B) B zero (initial R))
      (v (center A B) B (initial R) r) := by
  let z := center A B
  let N := initial R
  have tail : Γ ⊢[PRAAx] v z B (zero+N) r ≐ v z B N r := by
    ipra_congr (v (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _, .eqRefl _, zero_add N, .eqRefl _]
  exact (GaussianBarnesCanonicalSecondDerivativeTail.split z B zero N r).eqTrans (qadd_congr (.eqRefl _) tail)

theorem series_prefix_error (p A B R r : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalSecondDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 seriesF p (seriesData A B R)) (prefixValue A B R r) (num 4) (unit p) := by
  let z := center A B
  let a := v z B zero (initial R)
  let b := sd z R B
  have close := distance_symmetric _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (GaussianBarnesCanonicalSecondDerivativeCofinal.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalSecondDerivativeCofinal.late_prefix_error p z R B r h hr))
  have read := (qadd_congr (constant_at (Γ := Γ) p a) (.eqRefl _)).eqTrans (prefix_split A B R r).eqSymm
  exact distance_congr (.eqRefl _) read (by unfold three; ipra_ring) (.eqRefl _)
    (add_sample_error_right constantF S a b p _ one (constant_regular a)
      (GaussianBarnesCanonicalSecondDerivativeCofinal.regular z R B h) close)

theorem prefix_error (p A B R r : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalSecondDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B R)) (qadd
      (ap2 coefficientF p coefficientData) (prefixValue A B R r)) (num 7) (unit p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (add_sample_error_right coefficientF seriesF coefficientData (seriesData A B R) p _ (num 4)
      coefficient_regular (series_regular A B R h) (series_prefix_error p A B R r h hr))

theorem actual_Barnes_positive_second_logarithm_name_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (disk (center (var 0) (var 1)) (var 2) (var 1) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveSecondLogarithm
