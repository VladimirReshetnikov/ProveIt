import IPRADerivations.Analysis.Names.Rates.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.GaussianNamedReciprocalFrozenRate
import IPRADerivations.Analysis.Euler.GaussianEulerNamedPowerScalingPowerFrozen

/-!
# Compare an original named increment quotient with a decoded native quotient

The original numerator endpoints may be approximated by any two
regular names. The native increment is the actual later rational
observation of the original increment name. Its inverse error and
the two endpoint errors give a rate for the original quotient with
independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementQuotientFrozenRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerNamedPowerScalingPowerFrozen (constant_bound)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameReciprocal (anchor R R_positive modulus)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Q" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data
local notation "source" => GaussianNamedIncrementDifferenceQuotient.input
local notation "Qn" => GaussianNamedDifferenceQuotient.nameF
local notation "qnd" => GaussianNamedDifferenceQuotient.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "Rec" => GaussianNameReciprocal.nameF
local notation "rd" => GaussianNameReciprocal.nameData

def nativeNumerator (K : PR 2) (z k : PTm n) : PTm n := rawGaussian (ap2 K k z)
def nativeDenominator (K : PR 2) (z k : PTm n) : PTm n := rawDen (ap2 K k z)
def nativeData (L M K : PR 2) (u v z k : PTm n) : PTm n :=
  qnd L M u v (nativeNumerator K z k) (nativeDenominator K z k)
def differenceCap (F G : PR 2) (x y : PTm n) : PTm n := U (Diff F G) (dd x y)

def leadingNumerator (a k A C E W : PTm n) : PTm n := W*modulus a*E+R a*(A+C)*unit k
def leadingDenominator (k E : PTm n) : PTm n := unit k*E
def commonNumerator (a A C W : PTm n) : PTm n := W*modulus a+R a*(A+C)

@[simp] theorem subst_nativeNumerator {m : ℕ} (σ : Fin n → PTm m) (K : PR 2) (z k : PTm n) :
    Syn.subst σ (nativeNumerator K z k) = nativeNumerator K (Syn.subst σ z) (Syn.subst σ k) := by simp [nativeNumerator]

@[simp] theorem subst_nativeDenominator {m : ℕ} (σ : Fin n → PTm m) (K : PR 2) (z k : PTm n) :
    Syn.subst σ (nativeDenominator K z k) = nativeDenominator K (Syn.subst σ z) (Syn.subst σ k) := by simp [nativeDenominator]

@[simp] theorem subst_nativeData {m : ℕ} (σ : Fin n → PTm m) (L M K : PR 2) (u v z k : PTm n) :
    Syn.subst σ (nativeData L M K u v z k) =
      nativeData L M K (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ z) (Syn.subst σ k) := by simp [nativeData]

@[simp] theorem subst_differenceCap {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (x y : PTm n) :
    Syn.subst σ (differenceCap F G x y) = differenceCap F G (Syn.subst σ x) (Syn.subst σ y) := by simp [differenceCap]

@[simp] theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (a k A C E W : PTm n) :
    Syn.subst σ (leadingNumerator a k A C E W) = leadingNumerator (Syn.subst σ a) (Syn.subst σ k)
      (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ W) := by simp [leadingNumerator]

@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (k E : PTm n) :
    Syn.subst σ (leadingDenominator k E) = leadingDenominator (Syn.subst σ k) (Syn.subst σ E) := by simp [leadingDenominator]

@[simp] theorem subst_commonNumerator {m : ℕ} (σ : Fin n → PTm m) (a A C W : PTm n) :
    Syn.subst σ (commonNumerator a A C W) = commonNumerator (Syn.subst σ a) (Syn.subst σ A) (Syn.subst σ C) (Syn.subst σ W) :=
  by simp [commonNumerator]

theorem late_separated (K : PR 2) (a z k : PTm n) (hK : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hk : Γ ⊢[PRAAx] le (anchor a) k) :
    Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.separated (nativeNumerator K z k) (nativeDenominator K z k) :=
  .andI (raw_den_positive _) (GaussianNameReciprocal.lower_norm_positive _ _ (R_positive a)
    (GaussianNamedReciprocalFrozenRate.late_lower K a z k hK hk))

theorem late_value (K : PR 2) (z k : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ofGaussian (nativeNumerator K z k) (nativeDenominator K z k)) (ap2 K k z) zero one :=
  GaussianFastValueCut.recode_distance (ap2 K k z)

theorem native_regular (L M K : PR 2) (u v z a k : PTm n) (hL : Γ ⊢[PRAAx] pointCN L u)
    (hM : Γ ⊢[PRAAx] pointCN M v) (hK : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hk : Γ ⊢[PRAAx] le (anchor a) k) :
    Γ ⊢[PRAAx] pointCN (Qn L M) (nativeData L M K u v z k) :=
  GaussianNamedDifferenceQuotient.name_regular L M u v _ _ (.andI hL (.andI hM (late_separated K a z k hK hk)))

private theorem difference_rate (F G L M : PR 2) (x y u v A C E : PTm n)
    (hF : Γ ⊢[PRAAx] pointCN F x) (hG : Γ ⊢[PRAAx] pointCN G y)
    (hL : Γ ⊢[PRAAx] pointCN L u) (hM : Γ ⊢[PRAAx] pointCN M v) (hE : Γ ⊢[PRAAx] le one E)
    (hA : Γ ⊢[PRAAx] independentRate F L x u A E) (hC : Γ ⊢[PRAAx] independentRate G M y v C E) :
    Γ ⊢[PRAAx] independentRate (Diff F G) (Diff L M) (dd x y) (dd u v) (A+C) E := by
  have raw := GaussianNamedDifferenceRate.original_rate F G L M x y u v A E C E
    (.andI (.andI hE hE) (.andI (.andI hF hG) (.andI (.andI hL hM) (.andI hA hC))))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hE hE) hE
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedDifferenceRate.leadingNumerator,
      GaussianNamedDifferenceRate.leadingDenominator]; ipra_ring)) raw

theorem independent_rate (F G L M K : PR 2) (x y u v z a k A C E : PTm n)
    (hs : Γ ⊢[PRAAx] source F G K x y z a) (hL : Γ ⊢[PRAAx] pointCN L u)
    (hM : Γ ⊢[PRAAx] pointCN M v) (hk : Γ ⊢[PRAAx] le (anchor a) k) (hE : Γ ⊢[PRAAx] le one E)
    (hA : Γ ⊢[PRAAx] independentRate F L x u A E) (hC : Γ ⊢[PRAAx] independentRate G M y v C E) :
    Γ ⊢[PRAAx] independentRate (Q F G K) (Qn L M) (qd F G K x y z a) (nativeData L M K u v z k)
      (leadingNumerator a k A C E (differenceCap F G x y)) (leadingDenominator k E) := by
  let h := GaussianNamedReciprocalFrozenRate.frozen K z k
  let S := differenceCap F G x y
  have hF := hs.andE₁
  have hG := hs.andE₂.andE₁
  have hK := hs.andE₂.andE₂
  have dcn := GaussianNamedDifference.name_regular F G x y hF hG
  have ecn := GaussianNamedDifference.name_regular L M u v hL hM
  have inv := GaussianNameReciprocal.name_fast K a z hK.andE₁ hK.andE₂
  have hb : Γ ⊢[PRAAx] sampleBound (Diff F G) (dd x y) S := all_samples_bounded _ _ dcn
  have hc : Γ ⊢[PRAAx] sampleBound constantF h (R a) :=
    constant_bound h (R a) (GaussianNamedReciprocalFrozenRate.frozen_inverse_bound K a z k hK hk)
  exact GaussianNamedMultiplyRate.independent_rate (Rec K) (Diff F G) constantF (Diff L M) (rd a z) (dd x y)
    h (dd u v) (modulus a) (unit k) (A+C) E S (R a) (unit_positive k) hE inv dcn (constant_regular h) ecn hb hc
    (GaussianNamedReciprocalFrozenRate.frozen_rate K a z k hK hk)
    (difference_rate F G L M x y u v A C E hF hG hL hM hE hA hC)

private theorem precision_budget (X Y U E : PTm n) (h : Γ ⊢[PRAAx] le E U) :
    Γ ⊢[PRAAx] le ((X*E+Y*U)*E) ((X+Y)*(U*E)) := by
  have step := mul_le_mul_right (X*E) h
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ step (le_refl (Y*U*E)))

theorem common_precision_rate (F G L M K : PR 2) (x y u v z a k p A C : PTm n)
    (hs : Γ ⊢[PRAAx] source F G K x y z a) (hL : Γ ⊢[PRAAx] pointCN L u)
    (hM : Γ ⊢[PRAAx] pointCN M v) (hk : Γ ⊢[PRAAx] le (anchor a) k) (hp : Γ ⊢[PRAAx] le p k)
    (hA : Γ ⊢[PRAAx] independentRate F L x u A (unit p)) (hC : Γ ⊢[PRAAx] independentRate G M y v C (unit p)) :
    Γ ⊢[PRAAx] independentRate (Q F G K) (Qn L M) (qd F G K x y z a) (nativeData L M K u v z k)
      (commonNumerator a A C (differenceCap F G x y)) (unit p) := by
  let E := unit p
  let W := differenceCap F G x y
  have hE : Γ ⊢[PRAAx] le one E := unit_positive p
  have raw := independent_rate F G L M K x y u v z a k A C E hs hL hM hk hE hA hC
  exact GaussianNamedRateRadius.weaken (Q F G K) (Qn L M) (qd F G K x y z a) (nativeData L M K u v z k)
    (leadingNumerator a k A C E W) (leadingDenominator k E) (commonNumerator a A C W) E
    (positive_product _ _ (unit_positive k) hE) hE
    (precision_budget (W*modulus a) (R a*(A+C)) (unit k) E (GaussianExponentialReference.unit_monotone hp)) raw

theorem common_clock_rate (F G L M K : PR 2) (x y u v z a k A C : PTm n)
    (hs : Γ ⊢[PRAAx] source F G K x y z a) (hL : Γ ⊢[PRAAx] pointCN L u)
    (hM : Γ ⊢[PRAAx] pointCN M v) (hk : Γ ⊢[PRAAx] le (anchor a) k)
    (hA : Γ ⊢[PRAAx] independentRate F L x u A (unit k)) (hC : Γ ⊢[PRAAx] independentRate G M y v C (unit k)) :
    Γ ⊢[PRAAx] independentRate (Q F G K) (Qn L M) (qd F G K x y z a) (nativeData L M K u v z k)
      (commonNumerator a A C (differenceCap F G x y)) (unit k) :=
  common_precision_rate F G L M K x y u v z a k k A C hs hL hM hk (le_refl k) hA hC

theorem actual_named_increment_quotient_common_clock_frozen_closed (F G L M K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (let x := var 0
       let y := var 1
       let u := var 2
       let v := var 3
       let z := var 4
       let a := var 5
       let k := var 6
       let A := var 7
       let C := var 8
       (source F G K x y z a ⋏ (pointCN L u ⋏ (pointCN M v ⋏ (le (anchor a) k ⋏
         (independentRate F L x u A (unit k) ⋏ independentRate G M y v C (unit k)))))) ⟶
           independentRate (Q F G K) (Qn L M) (qd F G K x y z a) (nativeData L M K u v z k)
             (commonNumerator a A C (differenceCap F G x y)) (unit k)) :=
  closeUniv 9 (.impI (common_clock_rate F G L M K _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementQuotientFrozenRate
