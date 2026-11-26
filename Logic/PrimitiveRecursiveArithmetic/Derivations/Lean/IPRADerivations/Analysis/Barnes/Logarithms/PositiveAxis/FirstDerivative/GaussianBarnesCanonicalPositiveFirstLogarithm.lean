import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdLogarithmRows
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefactorExponentDerivative
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeCofinal
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# The original positive Barnes logarithm's first-derivative expression

Combine the original derivative of the prefactor exponent, the exact
finite kept first-derivative rows, and the cofinal sampler of the original
retained rows. A late prefix comparison retains the actual prefactor
observation at the requested clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalPrefactorExponentDerivative (derivativeData)
open GaussianBarnesCanonicalPrefactorInverse (exponentF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameRingLaws (add_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "S" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "sd" => GaussianBarnesCanonicalLogCofinal.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "v" => GaussianBarnesCanonicalDerivativeTail.value

def prefactorData (A B : PTm n) : PTm n := derivativeData (center A B) B

def seriesF : PR 2 := addF constantF S

def seriesData (A B R : PTm n) : PTm n := addData (v (center A B) B zero (initial R)) (sd (center A B) R B)

def nameF : PR 2 := addF exponentF seriesF

def data (A B R : PTm n) : PTm n := addData (prefactorData A B) (seriesData A B R)

def prefixValue (A B R r : PTm n) : PTm n := v (center A B) B zero (initial R+r)

@[simp] theorem subst_prefactorData {m : ℕ} (σ : Fin n → PTm m) (A B : PTm n) :
    Syn.subst σ (prefactorData A B) = prefactorData (Syn.subst σ A) (Syn.subst σ B) := by simp [prefactorData]

@[simp] theorem subst_seriesData {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (seriesData A B R) = seriesData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [seriesData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B R : PTm n) :
    Syn.subst σ (data A B R) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) := by simp [data]

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (A B R r : PTm n) :
    Syn.subst σ (prefixValue A B R r) = prefixValue (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ R) (Syn.subst σ r) :=
  by simp [prefixValue]

theorem prefactor_regular (A B : PTm n) : Γ ⊢[PRAAx] pointCN exponentF (prefactorData A B) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _

theorem series_regular (A B R : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] pointCN seriesF (seriesData A B R) :=
  add_fast _ _ _ _ (constant_regular _) (GaussianBarnesCanonicalDerivativeCofinal.regular _ _ _ h)

theorem regular (A B R : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B R) :=
  add_fast _ _ _ _ (prefactor_regular A B) (series_regular A B R h)

theorem prefix_split (A B R r : PTm n) :
    Γ ⊢[PRAAx] prefixValue A B R r ≐ qadd (v (center A B) B zero (initial R))
      (v (center A B) B (initial R) r) := by
  let z := center A B
  let N := initial R
  have tail : Γ ⊢[PRAAx] v z B (zero+N) r ≐ v z B N r := by
    ipra_congr (v (var 0) (var 1) (var 2) (var 3) : PTm 4)
      with [.eqRefl _, .eqRefl _, zero_add N, .eqRefl _]
  exact (GaussianBarnesCanonicalDerivativeTail.split z B zero N r).eqTrans (qadd_congr (.eqRefl _) tail)

theorem series_prefix_error (p A B R r : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 seriesF p (seriesData A B R)) (prefixValue A B R r) (num 4) (unit p) := by
  let z := center A B
  let N := initial R
  let a := v z B zero N
  let b := sd z R B
  have hu := unit_positive (Γ := Γ) p
  have e := GaussianBarnesCanonicalDerivativeCofinal.sample_at (Γ := Γ) p z R B
  have close := distance_symmetric _ _ _ _ hu
    (distance_congr (.eqRefl _) e.eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalDerivativeCofinal.late_prefix_error p z R B r h hr))
  have raw := add_sample_error constantF S a b p (constant_regular a)
    (GaussianBarnesCanonicalDerivativeCofinal.regular z R B h)
  have arc := sum_distance _ _ _ _ _ _ _ hu
    (distance_congr (constant_at p a).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero a (unit p) hu)) close
  have fit : Γ ⊢[PRAAx] GaussianNameRingLaws.three+(zero+one) ≐ num 4 := by unfold GaussianNameRingLaws.three; ipra_ring
  exact distance_congr (.eqRefl _) (prefix_split A B R r).eqSymm fit (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu raw arc)

theorem prefix_error (p A B R r : PTm n) (h : Γ ⊢[PRAAx] disk (center A B) R B)
    (hr : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalDerivativeCofinal.length p R) r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B R)) (qadd
      (ap2 exponentF p (prefactorData A B)) (prefixValue A B R r)) (num 7) (unit p) := by
  let u := ap2 exponentF p (prefactorData A B)
  have hu := unit_positive (Γ := Γ) p
  have main := add_sample_error exponentF seriesF (prefactorData A B) (seriesData A B R) p
    (prefactor_regular A B) (series_regular A B R h)
  have close := sum_distance _ _ _ _ _ _ _ hu
    (GaussianRationalPowerDifference.distance_refl_zero u (unit p) hu) (series_prefix_error p A B R r h hr)
  have fit : Γ ⊢[PRAAx] GaussianNameRingLaws.three+(zero+num 4) ≐ num 7 := by unfold GaussianNameRingLaws.three; ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) fit (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu main close)

theorem actual_Barnes_positive_first_logarithm_name_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (disk (center (var 0) (var 1)) (var 2) (var 1) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveFirstLogarithm
