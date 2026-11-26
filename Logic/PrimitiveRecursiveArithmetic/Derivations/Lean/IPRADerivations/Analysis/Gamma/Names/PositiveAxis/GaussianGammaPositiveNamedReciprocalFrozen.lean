import IPRADerivations.Analysis.Gamma.Digamma.PositiveNames.GaussianNamedPositiveDigamma
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianGammaPositiveNamedRationalFreeze
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate

/-!
# Freeze the certified reciprocal of the original positive Gamma

A single lower bound on positive real Gamma certifies named and native
reciprocal programs. The synthetic native reciprocal is identified with
the original C7 program by their exact inverse identities.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedReciprocalFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode re normSq)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN fraction fraction_represents)
open GaussianGammaDigammaNative (reciprocalData)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans diagonal_at cross_to_diagonal)
open GaussianNamedGammaFirstCrossing (inverseClock cancel_right)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNamedPositiveDigamma (source inverseF inverseData inverse_input)
open GaussianNamedRightHalfPlane (marginPoint threshold)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (bounded)
open GaussianStirlingGammaLogarithm (arg gammaData gamma_lower_at gammaMargin gamma_source gamma_regular)
open RationalValueBounds (upper upper_congr)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C7" => GaussianGammaC7Name.nameF
local notation "S" => GaussianNameReciprocal.nameF gammaF
local notation "gd" => GaussianNamedGamma.data
local notation "G" => GaussianNamedGamma.nameF
local notation "R" => GaussianNameReciprocal.R

def bound : PTm n := R inverseClock

def coefficient : PTm n := bound*bound

def nativeData (f : PR 2) (k x : PTm n) : PTm n :=
  reciprocalData (numerator f k x) (denominator f k x)

def syntheticData (a b : PTm n) : PTm n :=
  GaussianNameReciprocal.nameData inverseClock (gammaData a b)

@[simp] theorem subst_bound {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (bound : PTm n) = (bound : PTm m) := by
  simp [bound,inverseClock,one,two]

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (coefficient : PTm n) = (coefficient : PTm m) := by
  simp [coefficient]

@[simp] theorem subst_nativeData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (nativeData f k x) = nativeData f (Syn.subst σ k) (Syn.subst σ x) := by
  simp [nativeData]

@[simp] theorem subst_syntheticData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (syntheticData a b) = syntheticData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [syntheticData,inverseClock,one,two]

private theorem margin_positive : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by
  unfold gammaMargin
  ipra_le 17

private theorem margin_scalar : Γ ⊢[PRAAx]
    fstT (marginPoint (gammaMargin : PTm n)) ≐ fraction one gammaMargin := by
  have hD := margin_positive (Γ := Γ)
  apply RationalFiniteSum.canonical_equal _ _ (re oneCode) (ZT.ofNat one) _ _
    (ofGaussian_canonical oneCode _ hD).andE₂.andE₁ (RationalNormalForm.normalize_well_formed _ _ hD)
    (ofGaussian_represents oneCode _ hD).andE₁ (fraction_represents _ _ hD) hD hD
  apply ZT.derive
  simp only [ZT.toZ_mul,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one]

private theorem margin_paid : Γ ⊢[PRAAx] le (two*(gammaMargin : PTm n)) (unit inverseClock) := by
  let V : PTm n := two*gammaMargin
  have gain := GaussianFastValueCut.query_budget (Γ := Γ) V zero
  have product : Γ ⊢[PRAAx] V*one ≐ (two*gammaMargin) := by dsimp only [V]; ipra_ring
  exact le_congr ((congrMul (.eqRefl V) (pw_zero two)).eqTrans product) (.eqRefl _) gain

private theorem native_lower (p a b U : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b)
    (hp : Γ ⊢[PRAAx] le (two*gammaMargin) (unit p))
    (hU : Γ ⊢[PRAAx] le one U) (hu : Γ ⊢[PRAAx] le (two*gammaMargin) U) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.lower (ap2 gammaF p (gammaData a b)) U := by
  let q := ap2 gammaF p (gammaData a b)
  let z := rawGaussian q
  let d := rawDen q
  let V : PTm n := two*gammaMargin
  have read : Γ ⊢[PRAAx] upper (fstT (marginPoint gammaMargin)) (fstT q) one (unit p) :=
    upper_congr margin_scalar.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (gamma_lower_at p a b hs)
  have real := GaussianNamedRightHalfPlane.half_margin_from_upper q gammaMargin (unit p) margin_positive
    (unit_positive p) hp read
  have pole := GaussianGammaRightHalfPlane.real_margin_pole_at z d V zero real
  have norm := GaussianRootAlgebra.normSq_equal (GaussianGammaEulerHeadLower.translated_zero (Γ := Γ) z d)
  have first : Γ ⊢[PRAAx] le (d*d) (V*V*normSq z) :=
    le_congr (by ipra_ring) (congrMul (.eqRefl _) norm) pole
  have squares : Γ ⊢[PRAAx] le (V*V) (U*U) :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right V hu)) (mul_le_mul_right U hu)
  exact GaussianRationalLowerBounds.lower_from_representation q z d one U (raw_den_positive q)
    hU (raw_represents q)
    (le_congr (by ipra_ring) (.eqRefl _) (le_trans first (mul_le_mul_right (normSq z) squares)))

theorem rational_apart (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.apart gammaF inverseClock (gammaData a b) := by
  let p : PTm n := GaussianNameReciprocal.anchor inverseClock
  have later : Γ ⊢[PRAAx] le (unit (inverseClock : PTm n)) (unit p) :=
    GaussianExponentialReference.unit_monotone (le_add_right _ _)
  exact native_lower p a b (unit inverseClock) hs (le_trans margin_paid later)
    (unit_positive _) margin_paid

theorem synthetic_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] pointCN S (syntheticData a b) :=
  GaussianNameReciprocal.name_fast gammaF inverseClock (gammaData a b) (gamma_regular a b hs) (rational_apart a b hs)

theorem synthetic_cross (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent S C7 (syntheticData a b) (reciprocalData a b) := by
  let x := gammaData a b
  let y := syntheticData a b
  let z := reciprocalData a b
  have hG := gamma_regular a b hs
  have apart := rational_apart a b hs
  have u := GaussianNameReciprocal.product_one_left gammaF inverseClock x hG apart
  have v := GaussianGammaReciprocalInverse.gamma_product (arg a) a b one b (gamma_source a b hs)
  have e := cross_trans _ _ _ _ _ _ u
    (cross_trans _ _ _ _ _ _ (GaussianBoundedInverseApartness.ones_equivalent x z) (cross_symm _ _ _ _ v))
  exact cancel_right S C7 gammaF y z x inverseClock (synthetic_regular a b hs)
    (GaussianGammaDigammaNative.reciprocal_regular a b hs) hG apart e

private theorem synthetic_observation_bound (f : PR 2) (p x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNameReciprocal.input f inverseClock x) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianNameReciprocal.nameF f) p (GaussianNameReciprocal.nameData inverseClock x)) bound one := by
  let t := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus inverseClock) p
  let u := GaussianNameReciprocal.raw f inverseClock x t
  have b := GaussianNameReciprocal.raw_bound f inverseClock x t h.andE₁ h.andE₂
  exact GaussianRationalReciprocal.bound_congr (GaussianNameReciprocal.name_at f inverseClock x p).eqSymm
    (.eqRefl _) (.eqRefl _) ((GaussianFastValueCut.recode_bound_iff u bound one (le_refl one)).iffMpr b)

private theorem synthetic_bounded (f : PR 2) (x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNameReciprocal.input f inverseClock x) : Γ ⊢[PRAAx]
    sampleBound (GaussianNameReciprocal.nameF f) (GaussianNameReciprocal.nameData inverseClock x) bound := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] GaussianNameReciprocal.input f inverseClock (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift,inverseClock,one,two] using h.shift
  refine .allI ?_
  simpa [Syn.shift,inverseClock,one,two] using synthetic_observation_bound f (var 0) (Syn.shift x) hh

theorem named_bounded (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] sampleBound (inverseF f) (inverseData x A) bound :=
  synthetic_bounded (G f) (gd x A) (inverse_input f x A h)

private theorem native_sharp_bound (p a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) : Γ ⊢[PRAAx]
    bounded (ap2 S p (syntheticData a b)) (two*gammaMargin) one := by
  let V : PTm n := two*gammaMargin
  let x := gammaData a b
  let t := GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus inverseClock) p
  let k := t+GaussianNameReciprocal.anchor inverseClock
  have later : Γ ⊢[PRAAx] le (inverseClock : PTm n) k :=
    le_trans (le_add_right _ _) (le_add_left _ _)
  have hV : Γ ⊢[PRAAx] le one V := by unfold V gammaMargin; ipra_le 35
  have hl := native_lower k a b V hs (le_trans margin_paid (GaussianExponentialReference.unit_monotone later)) hV (le_refl V)
  have raw := GaussianNameReciprocal.inverse_bound (ap2 gammaF k x) V hV hl
  exact GaussianRationalReciprocal.bound_congr (GaussianNameReciprocal.name_at gammaF inverseClock x p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff (GaussianNameReciprocal.raw gammaF inverseClock x t) V one (le_refl one)).iffMpr raw)

theorem rational_observation_bounded (p a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] bounded (ap2 C7 p (reciprocalData a b)) bound one := by
  let V : PTm n := two*gammaMargin
  let H : PTm n := inverseClock
  let x := ap2 C7 p (reciprocalData a b)
  let y := ap2 S p (syntheticData a b)
  have near := diagonal_at C7 S (reciprocalData a b) (syntheticData a b) p
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (synthetic_cross a b hs)))
  have dist := distance_radius_mono x y two (unit p) two one (unit_positive p) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two (unit_positive p))) near
  have disk := GaussianReconstructionRoots.norm_from_distance x y two one V one
    (le_refl one) (le_refl one) dist (native_sharp_bound p a b hs)
  have v : Γ ⊢[PRAAx] le two V := by unfold V gammaMargin; ipra_le 34
  have paid : Γ ⊢[PRAAx] le (two+V) (unit H+unit H) :=
    add_le_add₂ (le_trans v margin_paid) margin_paid
  have double : Γ ⊢[PRAAx] unit H+unit H ≐ (bound : PTm n) := by
    change Γ ⊢[PRAAx] unit H+unit H ≐ pw two (LeanProofs.ConciseIPRA.PTm.succ H)
    exact (by unfold unit; ipra_ring : Γ ⊢[PRAAx] unit H+unit H ≐ unit H*two).eqTrans (pw_succ two H).eqSymm
  have reduced : Γ ⊢[PRAAx] bounded x (two+V) one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) disk
  exact bounded_radius_mono x (two+V) one bound one (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (le_congr (.eqRefl _) double paid))
    reduced

theorem rational_bounded (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] sampleBound C7 (reciprocalData a b) bound := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (Syn.shift a) (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa [Syn.shift] using rational_observation_bounded (var 0) (Syn.shift a) (Syn.shift b) hs

theorem original_rate (f : PR 2) (s k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (GaussianGammaPositiveNamedRationalFreeze.clock f s one x A) k) :
    Γ ⊢[PRAAx] independentRate (inverseF f) C7 (inverseData x A) (nativeData f k x) coefficient (unit s) := by
  let a := numerator f k x
  let b := denominator f k x
  let v := syntheticData a b
  have hT : Γ ⊢[PRAAx] le (threshold A) k :=
    le_trans (GaussianGammaPositiveNamedRationalFreeze.threshold_le f s one x A) hk
  have ha := (frozen_rational_domain f k x A h hT).andE₁
  have hi := inverse_input f x A h
  have hj : Γ ⊢[PRAAx] GaussianNameReciprocal.input gammaF inverseClock (gammaData a b) :=
    .andI (gamma_regular a b ha) (rational_apart a b ha)
  have i := GaussianNameReciprocal.product_one (G f) inverseClock (gd x A) hi.andE₁ hi.andE₂
  have j := GaussianNameReciprocal.product_one gammaF inverseClock (gammaData a b) hj.andE₁ hj.andE₂
  have native := GaussianGammaPositiveNamedRationalFreeze.gamma_rate f s one k x A h hk
  have uniform (F : PR 2) (u : PTm n) (hu : Γ ⊢[PRAAx] sampleBound F u bound) :
      Γ ⊢[PRAAx] GaussianExponentialSmallPerturbation.smallSamples F u bound one := by
    simpa only [sampleBound,GaussianExponentialSmallPerturbation.smallSamples,Syn.shift,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hu
  have inverse := GaussianNamedInverseRate.inverse_rate (G f) gammaF (inverseF f) S
    (gd x A) (gammaData a b) (inverseData x A) v bound one one (unit s)
    (.andI (le_refl one) (.andI (unit_positive s) (.andI (.andI hi.andE₁ hj.andE₁)
      (.andI (.andI (GaussianNamedPositiveDigamma.inverse_regular f x A h) (synthetic_regular a b ha))
        (.andI (.andI (uniform _ _ (named_bounded f x A h)) (uniform _ _ (synthetic_bounded gammaF (gammaData a b) hj)))
          (.andI (.andI i j) native))))))
  have fix := GaussianNamedDifferenceRate.rate_parameters_congr (inverseF f) S (inverseData x A) v
    _ _ coefficient (unit s) (by unfold coefficient; ipra_ring) (by ipra_ring) inverse
  exact GaussianNamedRateTransport.transport (inverseF f) S (inverseF f) C7
    (inverseData x A) v (inverseData x A) (nativeData f k x) coefficient (unit s) (unit_positive s) fix
    (cross_refl _ _ (GaussianNamedPositiveDigamma.inverse_regular f x A h))
    (cross_symm _ _ _ _ (synthetic_cross a b ha))

theorem actual_original_positive_Gamma_reciprocal_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 2) (var 3) ⋏
        le (GaussianGammaPositiveNamedRationalFreeze.clock f (var 0) one (var 2) (var 3)) (var 1)) ⟶
        independentRate (inverseF f) C7 (inverseData (var 2) (var 3)) (nativeData f (var 1) (var 2))
          coefficient (unit (var 0))) :=
  closeUniv 4 (.impI (original_rate f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedReciprocalFrozen
