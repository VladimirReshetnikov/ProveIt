import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedTranslatedPower
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFrozen

/-!
# Exact local factorization on regular named Barnes inputs

A common late original Gaussian observation binds the existing named
Barnes value, the named translated power and the named deflated
coefficient to their rational evaluations. The exact rational
factorization then identifies the actual named product.
-/

set_option autoImplicit false
set_option maxHeartbeats 1550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedLocalFactorization

open_ipra
open GaussianBarnesCanonicalDeflatedNamed (source neighborhood rational_source neighborhood_at)
open GaussianBarnesCanonicalDeflatedValue (headCoefficientF headCoefficientData remainingLength)
open GaussianBarnesCanonicalDeflatedValueContinuity (tailCap)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast product_distance)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal diagonal_at)
open GaussianNamedBoundedProductObservation (sample_bounds sample_error)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same distance_radius_mono_den)
open GaussianRationalHorner (qmul)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "W" => GaussianBarnesCanonicalDeflatedValue.nameF
local notation "Wd" => GaussianBarnesCanonicalDeflatedValue.data
local notation "Q" => GaussianBarnesCanonicalNamedTranslatedPower.nameF
local notation "Qd" => GaussianBarnesCanonicalNamedTranslatedPower.data
local notation "U" => GaussianBarnesCanonicalDeflatedNamed.nameF
local notation "Ud" => GaussianBarnesCanonicalDeflatedNamed.data
local notation "F" => GaussianBarnesCanonicalNamed.nameF
local notation "Fd" => GaussianBarnesCanonicalNamedDemand.data
local notation "Pcap" => GaussianBarnesCanonicalDiskBound.prefactorBound
local notation "Hcap" => GaussianBarnesCanonicalDeflatedHeadLipschitz.cap

def nameF (f : PR 2) : PR 2 := multiplyF (Q f) (U f)
def data (f : PR 2) (x R m : PTm n) : PTm n := multiplyData (Q f) (U f) (Qd x m) (Ud x R m)

def cap (R m : PTm n) : PTm n := Hcap R m (remainingLength R m)*(Pcap R*tailCap R)

def cost (f : PR 2) (x R m : PTm n) : PTm n :=
  ((num 3+two)+two*(one+cap R m))+(two*cap R m+one*two)+
    (multiplyModulus (Q f) (U f) (Qd x m) (Ud x R m)+one)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x R m : PTm n) :
    Syn.subst σ (data f x R m) = data f (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by simp [data]

@[simp] theorem subst_cost {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x R m : PTm n) :
    Syn.subst σ (cost f x R m) = cost f (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by
  simp [cost,cap,tailCap,remainingLength,GaussianBarnesCanonicalDeflatedHeadLipschitz.cap,
    GaussianBarnesCanonicalDeflatedHeadLipschitz.multiplierCap,GaussianBarnesCanonicalDeflatedHeadLipschitz.skippedCap,
    GaussianBarnesCanonicalFactor.exponentRadius,one,two]

private theorem prefactor_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] sampleBound GaussianBarnesCanonicalPrefactor.nameF (GaussianBarnesCanonicalPrefactor.data z B) (Pcap R) := by
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (s z) (s R) (s B) := by
    simpa [Fm.shift,Syn.shift,s] using h.shift
  simpa only [sampleBound,Syn.shift,s,GaussianBarnesCanonicalPrefactor.subst_data,
    GaussianBarnesCanonicalDiskBound.subst_prefactorBound] using
    GaussianBarnesCanonicalDiskBound.prefactor_sample_bound (var 0) (s z) (s R) (s B) hs

theorem coefficient_bound (z R B m : PTm n) (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source z R B m) :
    Γ ⊢[PRAAx] sampleBound W (Wd z R B m) (cap R m) := by
  have hz : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B := .andI h.andE₁ h.andE₂.andE₂
  have outer := sample_bounds GaussianBarnesCanonicalPrefactor.nameF GaussianBarnesCanonicalTailExponential.nameF
    (GaussianBarnesCanonicalPrefactor.data z B) (GaussianBarnesCanonicalTailExponential.data z R B) (Pcap R) (tailCap R)
    (prefactor_bound z R B hz) (GaussianBarnesCanonicalTailContinuity.sample_bound z R B hz)
  exact sample_bounds headCoefficientF GaussianBarnesCanonicalDeflatedValue.outerF
    (headCoefficientData z R B m (remainingLength R m)) (GaussianBarnesCanonicalDeflatedValue.outerData z R B) _ _
    (GaussianBarnesCanonicalDeflatedHeadLipschitz.sample_bound z R B m (remainingLength R m) h) outer

theorem regular (f : PR 2) (x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m)
    (hn : Γ ⊢[PRAAx] neighborhood f x m) : Γ ⊢[PRAAx] pointCN (nameF f) (data f x R m) :=
  multiply_fast (Q f) (U f) _ _
    (GaussianBarnesCanonicalNamedTranslatedPower.regular f x m h.andE₁.andE₁ hn)
    (GaussianBarnesCanonicalDeflatedNamed.regular f x R m h)

private theorem later_to_earlier (a b A p q : PTm n) (hpq : Γ ⊢[PRAAx] le p q)
    (h : Γ ⊢[PRAAx] distanceBounded a b A (unit q)) : Γ ⊢[PRAAx] distanceBounded a b A (unit p) :=
  distance_radius_mono_den (unit_positive p) (unit_monotone hpq) h

private theorem value_readback (f : PR 2) (p k x R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source f x R)
    (hk : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalNamed.clock p R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (F f) p (Fd x R))
      (ap2 V (succ p) (GaussianBarnesCanonicalNamedDemand.frozenData f k x R)) (num 3) (unit p) := by
  let A := unit p
  let B := unit (succ p)
  have grow : Γ ⊢[PRAAx] le A B := unit_monotone (le_succ_self p)
  have guard : Γ ⊢[PRAAx] le (rateNumerator one A p (succ p)*A)
      (num 3*rateDenominator A p (succ p)) := by
    change Γ ⊢[PRAAx] le ((one*A*B+A*(A+B))*A) (num 3*(A*A*B))
    ipra_le 𝔞 A^2*sl grow
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive p)) (unit_positive p) guard
    (rate_at _ _ _ _ _ _ p (succ p) (GaussianBarnesCanonicalNamedFrozen.frozen_rate f p k x R h hk))

private theorem coefficient_readback (f : PR 2) (p k x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m)
    (hk : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalDeflatedNamed.clock p R m) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 W (succ p) (GaussianBarnesCanonicalDeflatedNamed.frozenData f k x R m))
      (ap2 (U f) p (Ud x R m)) two (unit p) := by
  let t := GaussianBarnesCanonicalDeflatedNamed.clock p R m
  have obs := GaussianBarnesCanonicalDeflatedNamed.late_observations f f p p k t x x R m h h
    (cross_refl _ _ h.andE₁.andE₁) hk (le_refl _)
  have pay := distance_radius_mono _ _ _ _ two (unit p)
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) obs
  exact distance_congr (.eqRefl _) (GaussianBarnesCanonicalDeflatedNamed.sample_at f p x R m).eqSymm (.eqRefl _) (.eqRefl _) pay

private theorem observation (f : PR 2) (p x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m)
    (hn : Γ ⊢[PRAAx] neighborhood f x m) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (F f) p (Fd x R)) (ap2 (nameF f) p (data f x R m)) (cost f x R m) (unit p) := by
  let a := GaussianBarnesCanonicalNamed.clock p R
  let b := GaussianBarnesCanonicalDeflatedNamed.clock p R m
  let k := a+(b+exponent m p)
  let q := ap2 f k x
  let z := rawGaussian q
  let B := rawDen q
  let A := unit p
  let c := cap R m
  let s := succ p
  let w := GaussianBarnesCanonicalNamedTranslatedPower.frozen f k x m
  let y := Wd z R B m
  let l := Qd x m
  let r := Ud x R m
  have hA := unit_positive (Γ := Γ) p
  have hB := rational_source f k x R m h
  have hNear := neighborhood_at f k x m hn
  have first := value_readback f p k x R h.andE₁ (le_add_right _ _)
  have regularW := GaussianBarnesCanonicalDeflatedValue.regular z R B m hB
  have regularQ : Γ ⊢[PRAAx] pointCN constantF w := constant_regular w
  have fact := GaussianBarnesCanonicalDeflatedValue.original_factorization z R B m hB hNear
  have second := later_to_earlier _ _ two p s (le_succ_self p)
    (diagonal_at _ _ _ _ s (cross_to_diagonal _ _ _ _ fact))
  have bounds := coefficient_bound z R B m hB
  have twoFactors := sample_error constantF W s w y one c regularQ regularW
    (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound w one
      (GaussianBarnesCanonicalNamedTranslatedPower.frozen_bound f k x m hn)) bounds
  have sampleEq := constant_at (Γ := Γ) s w
  have third := later_to_earlier _ _ _ p s (le_succ_self p)
    (distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr sampleEq (.eqRefl _))
      (.eqRefl _) (.eqRefl _) twoFactors)
  have hPow := GaussianBarnesCanonicalNamedTranslatedPower.late_observation f p k x m h.andE₁.andE₁ hn
    (le_trans (le_add_left _ _) (le_add_left _ _))
  have hCoeff := coefficient_readback f p k x R m h (le_trans (le_add_right _ _) (le_add_left _ _))
  have leftBounds := GaussianNamedMultiplyRate.sample_bound_at W y c s bounds
  have rightBounds := GaussianNamedMultiplyRate.sample_bound_at (Q f) l one p
    (GaussianBarnesCanonicalNamedTranslatedPower.name_bound f x m hn)
  have fourth := product_distance w (ap2 (Q f) p l) (ap2 W s y) (ap2 (U f) p r) two two A c one hA
    (distance_symmetric _ _ _ _ hA hPow) hCoeff leftBounds rightBounds
  have fifth := distance_symmetric _ _ _ _ hA
    (GaussianNameRingLaws.multiply_sample_error (Q f) (U f) l r p
      (GaussianBarnesCanonicalNamedTranslatedPower.regular f x m h.andE₁.andE₁ hn)
      (GaussianBarnesCanonicalDeflatedNamed.regular f x R m h))
  exact distance_triangle_same _ _ _ _ _ _ hA
    (distance_triangle_same _ _ _ _ _ _ hA
      (distance_triangle_same _ _ _ _ _ _ hA (distance_triangle_same _ _ _ _ _ _ hA first second) third) fourth) fifth

theorem original_factorization (f : PR 2) (x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m)
    (hn : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] crossEquivalent (F f) (nameF f) (Fd x R) (data f x R m) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost f x R m)
    (GaussianBarnesCanonicalNamed.name_regular f x R h.andE₁) (regular f x R m h hn)
  refine .allI ?_
  let s (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] source f (s x) (s R) (s m) := by simpa [Fm.shift,Syn.shift,s,Δ] using h.shift
  have hn' : Δ ⊢[PRAAx] neighborhood f (s x) (s m) := by simpa [Fm.shift,Syn.shift,s,Δ] using hn.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianBarnesCanonicalNamedDemand.subst_data,
    subst_data,subst_cost,Syn.shift,s,Δ] using observation f (var 0) (s x) (s R) (s m) h' hn'

theorem actual_Barnes_named_local_factorization_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source f (var 0) (var 1) (var 2) ⋏ neighborhood f (var 0) (var 2)) ⟶
      (crossEquivalent (F f) (nameF f) (Fd (var 0) (var 1)) (data f (var 0) (var 1) (var 2)) ⋏
       GaussianNameReciprocal.apart (U f) (GaussianBarnesCanonicalDeflatedNamed.height (var 1) (var 2))
         (Ud (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.andI (original_factorization f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (GaussianBarnesCanonicalDeflatedNamed.original_apart f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedLocalFactorization
