import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreezeRational
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreezeLocation
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreezeOrder

/-!
# Transfer cofinal rational minimum comparisons to the original named Gamma

Both original inputs are frozen at one query that meets their continuity
demands. The observations of the corresponding log Gamma names retain
the requested output precision. A uniform rational comparison at those
frozen points then gives exact real order at the original names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaDigammaDyadicLocation (locationF lower)
open GaussianGammaDigammaDyadicMesh (grid)
open GaussianGammaDigammaLocationInput (named_real_source)
open GaussianGammaMinimumFreeze (nameF data name_regular)
open GaussianGammaMinimumFreezeLocation (frozen_root_log_rate)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_log_rate frozen_rational_domain)
open GaussianNamedGammaPositiveLower (source clock)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRightHalfPlane (threshold)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData gammaLogMargin gammaMargin)
open RationalValueBounds (upper upper_of_radius radius_symmetric upper_triangle upper_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "M" => GaussianNamedRightHalfPlane.radius
local notation "modulus" => GaussianGammaHalfPlaneInputContinuity.modulus
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data

def lateClock (f : PR 2) (p x y A : PTm n) : PTm n :=
  p+(clock locationF p x one+clock f p y A)

def comparisonRadius (f : PR 2) (y : PTm n) : PTm n := M f y+two

def rootObservation (p k : PTm n) : PTm n :=
  fstT (ap2 logGammaF p (logGammaData (lower k) (grid k)))

def comparisonObservation (f : PR 2) (p k y : PTm n) : PTm n :=
  fstT (ap2 logGammaF p (logGammaData (numerator f k y) (denominator f k y)))

def nativeAt (f : PR 2) (p x y A C : PTm n) : Fm PTm n :=
  let k := lateClock f p x y A
  upper (rootObservation p k) (comparisonObservation f p k y)
    (C*unit p+two*unit k) (unit k*unit p)

def nativeComparison (f : PR 2) (x y A C : PTm n) : Fm PTm n :=
  .all (nativeAt f (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift C))

@[simp] theorem subst_lateClock {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x y A : PTm n) :
    Syn.subst σ (lateClock f p x y A) =
      lateClock f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) := by
  simp [lateClock]

@[simp] theorem subst_comparisonRadius {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (y : PTm n) :
    Syn.subst σ (comparisonRadius f y) = comparisonRadius f (Syn.subst σ y) := by
  simp [comparisonRadius]

@[simp] theorem subst_rootObservation {m : ℕ} (σ : Fin n → PTm m) (p k : PTm n) :
    Syn.subst σ (rootObservation p k) = rootObservation (Syn.subst σ p) (Syn.subst σ k) := by
  simp [rootObservation]

@[simp] theorem subst_comparisonObservation {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p k y : PTm n) :
    Syn.subst σ (comparisonObservation f p k y) =
      comparisonObservation f (Syn.subst σ p) (Syn.subst σ k) (Syn.subst σ y) := by
  simp [comparisonObservation]

@[simp] theorem subst_nativeAt {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x y A C : PTm n) :
    (nativeAt f p x y A C).subst σ =
      nativeAt f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ C) := by
  simp [nativeAt]

@[simp] theorem subst_nativeComparison {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x y A C : PTm n) :
    (nativeComparison f x y A C).subst σ =
      nativeComparison f (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ C) := by
  simp [nativeComparison, Syn.subst_shift, Syn.shift_subst]

theorem native_at (f : PR 2) (p x y A C : PTm n) (h : Γ ⊢[PRAAx] nativeComparison f x y A C) :
    Γ ⊢[PRAAx] nativeAt f p x y A C := by
  simpa only [nativeComparison, subst_nativeAt, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h.allE p

theorem late_clock_bounds (f : PR 2) (p x y A : PTm n) :
    Γ ⊢[PRAAx] le p (lateClock f p x y A) ⋏
      (le (clock locationF p x one) (lateClock f p x y A) ⋏ le (clock f p y A) (lateClock f p x y A)) :=
  .andI (le_add_right _ _) (.andI (le_trans (le_add_right _ _) (le_add_left _ _))
    (le_trans (le_add_left _ _) (le_add_left _ _)))

theorem comparison_domain (f : PR 2) (p x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    let k := lateClock f p x y A
    let c := numerator f k y
    let d := denominator f k y
    Γ ⊢[PRAAx] (le one c ⋏ le one d) ⋏
      (le two (comparisonRadius f y) ⋏ le c (comparisonRadius f y*d)) := by
  let k := lateClock f p x y A
  let d := denominator f k y
  have hk := (late_clock_bounds (Γ := Γ) f p x y A).andE₂.andE₂
  have ht : Γ ⊢[PRAAx] le (threshold A) k := le_trans (le_add_right _ _) hk
  have h := frozen_rational_domain f k y A hs ht
  have widen : Γ ⊢[PRAAx] le (M f y*d) (comparisonRadius f y*d) := by
    unfold comparisonRadius
    ipra_le 2*𝔞 d
  exact .andI h.andE₁ (.andI (le_add_left _ _) (le_trans h.andE₂.andE₂ widen))

private theorem diagonal_radius (F H : PR 2) (p u v : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F H u v gammaLogMargin (unit p)) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (fstT (ap2 F p u)) (fstT (ap2 H p v)) (num 38) (unit p) := by
  have U := unit_positive (Γ := Γ) p
  have d := rate_at F H u v gammaLogMargin (unit p) p p h
  apply scalar_coordinate_distance _ _ _ _ U
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ U) U ?_ d
  apply le_of_eq_add (d := zero)
  unfold rateNumerator rateDenominator gammaLogMargin gammaMargin
  ipra_ring

theorem frozen_radii (f : PR 2) (p x y A : PTm n) (hs : Γ ⊢[PRAAx] source f y A) :
    let k := lateClock f p x y A
    Γ ⊢[PRAAx]
      (RationalValueBounds.radius (fstT (ap2 (nameF locationF) p (data x one)))
        (rootObservation p k) (num 38) (unit p) ⋏
       RationalValueBounds.radius (fstT (ap2 (nameF f) p (data y A)))
        (comparisonObservation f p k y) (num 38) (unit p)) := by
  let k := lateClock f p x y A
  have hk := late_clock_bounds (Γ := Γ) f p x y A
  have left := diagonal_radius (nameF locationF) logGammaF p (data x one) (logGammaData (lower k) (grid k))
    (frozen_root_log_rate p k x (le_trans (le_add_right _ _) hk.andE₂.andE₁)
      (le_trans (le_add_left _ _) hk.andE₂.andE₁))
  have right := diagonal_radius (nameF f) logGammaF p (data y A)
    (logGammaData (numerator f k y) (denominator f k y))
    (frozen_log_rate f p k y A hs (le_trans (le_add_right _ _) hk.andE₂.andE₂)
      (le_trans (le_add_left _ _) hk.andE₂.andE₂))
  exact .andI left right

theorem observation_bound (f : PR 2) (p x y A C : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (hn : Γ ⊢[PRAAx] nativeAt f p x y A C) :
    Γ ⊢[PRAAx] upper (fstT (ap2 (nameF locationF) p (data x one)))
      (fstT (ap2 (nameF f) p (data y A))) (C+num 78) (unit p) := by
  let k := lateClock f p x y A
  let U := unit p
  let K := unit k
  let a := fstT (ap2 (nameF locationF) p (data x one))
  let b := fstT (ap2 (nameF f) p (data y A))
  let E := rootObservation p k
  let F := comparisonObservation f p k y
  have hk := late_clock_bounds (Γ := Γ) f p x y A
  have hu := unit_positive (Γ := Γ) p
  have hku := positive_product _ _ (unit_positive k) hu
  have grow : Γ ⊢[PRAAx] le U K := unit_monotone hk.andE₁
  have radii := frozen_radii f p x y A hs
  have first : Γ ⊢[PRAAx] upper a E (num 38) U := upper_of_radius _ _ _ _ radii.andE₁
  have last : Γ ⊢[PRAAx] upper F b (num 38) U := upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ radii.andE₂)
  have middle : Γ ⊢[PRAAx] upper E F (C+two) U := by
    apply upper_mono _ _ _ _ _ _ hku hn
    change Γ ⊢[PRAAx] le ((C*U+two*K)*U) ((C+two)*(K*U))
    ipra_le 𝔞 C*𝔞 U*sl grow
  have lu := positive_product _ _ hu hu
  have join := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ first middle) last
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ lu hu) join
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem log_order_of_native (f : PR 2) (x y A C : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (hn : Γ ⊢[PRAAx] nativeComparison f x y A C) :
    Γ ⊢[PRAAx] realOrder (nameF locationF) (nameF f) (data x one) (data y A) := by
  apply order_from_envelope _ _ _ _ (C+num 78)
    (name_regular locationF x one (named_real_source x)) (name_regular f y A hs)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let Y := Syn.shift y
  let B := Syn.shift A
  let K := Syn.shift C
  let p : PTm (n+1) := var 0
  have h : Δ ⊢[PRAAx] source f Y B := by
    simpa only [Δ, Y, B, Fm.shift, Syn.shift, GaussianNamedGammaPositiveLower.subst_source] using hs.shift
  have nat : Δ ⊢[PRAAx] nativeComparison f X Y B K := by
    simpa only [Δ, X, Y, B, K, Fm.shift, Syn.shift, subst_nativeComparison] using hn.shift
  simpa only [envelope, GaussianGammaMinimumFreeze.subst_data, Syn.shift, X, Y, B, K, p,
    PTm.subst_add, PTm.subst_num, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    observation_bound f p X Y B K h (native_at f p X Y B K nat)

theorem weak_minimum_of_native (f : PR 2) (x y A C : PTm n)
    (hs : Γ ⊢[PRAAx] source f y A) (hn : Γ ⊢[PRAAx] nativeComparison f x y A C) :
    Γ ⊢[PRAAx] realOrder (G locationF) (G f) (gd x one) (gd y A) :=
  GaussianGammaMinimumFreezeOrder.order_from_log locationF f x y one A (named_real_source x) hs
    (log_order_of_native f x y A C hs hn)

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumGlobalComparison
