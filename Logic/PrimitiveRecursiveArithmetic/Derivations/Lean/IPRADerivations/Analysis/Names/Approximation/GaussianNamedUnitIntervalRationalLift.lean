import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianNamedEulerUnitTime
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalExponent

/-!
# Lift a rational evaluation with a uniform rate to unit-interval names

The map takes a numerator, denominator, and an internal parameter.
Its rational Lipschitz theorem is used under arbitrary object-theory
contexts. A demand clock normalizes the actual primitive-recursive
samples and also bounds the distance to every sufficiently late
rational input observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianNamedUnitIntervalRationalLift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget recode_distance_bound)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianNamedEulerUnitTime (source source_at encoded_source)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "compact" => GaussianEulerUnitCompactTimeBounds.source

structure RationalMap where
  evaluator : PR 3
  gain : {m : ℕ} → PTm m → PTm m → PTm m
  subst_gain : ∀ {i j : ℕ} (σ : Fin i → PTm j) (E N : PTm i),
    Syn.subst σ (gain E N) = gain (Syn.subst σ E) (Syn.subst σ N)
  variation : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (a b c d E N A D : PTm m),
    (Δ ⊢[PRAAx] compact a b E) → (Δ ⊢[PRAAx] compact c d E) → (Δ ⊢[PRAAx] le one D) →
    (Δ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) →
      (Δ ⊢[PRAAx] distanceBounded (ap3 evaluator a b N) (ap3 evaluator c d N) (gain E N*A) D)

def clock (R : RationalMap) (p E N : PTm n) : PTm n := exponent (R.gain E N) p

def frozen (R : RationalMap) (f : PR 2) (k x N : PTm n) : PTm n :=
  ap3 R.evaluator (numerator (ap2 f k x)) (denominator (ap2 f k x)) N

def sample (R : RationalMap) (f : PR 2) (p x E N : PTm n) : PTm n :=
  frozen R f (clock R p E N) x N

def data (x E N : PTm n) : PTm n := pairT x (pairT E N)

def nameF (R : RationalMap) (f : PR 2) : PR 2 := PTm.toPR
  (sample R f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (R : RationalMap) (p E N : PTm n) :
    Syn.subst σ (clock R p E N) = clock R (Syn.subst σ p) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [clock, R.subst_gain]

@[simp] theorem subst_frozen {m : ℕ} (σ : Fin n → PTm m) (R : RationalMap) (f : PR 2) (k x N : PTm n) :
    Syn.subst σ (frozen R f k x N) = frozen R f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ N) := by
  simp [frozen]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (R : RationalMap) (f : PR 2) (p x E N : PTm n) :
    Syn.subst σ (sample R f p x E N) = sample R f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [sample]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x E N : PTm n) :
    Syn.subst σ (data x E N) = data (Syn.subst σ x) (Syn.subst σ E) (Syn.subst σ N) := by simp [data]

theorem sample_at (R : RationalMap) (f : PR 2) (p x E N : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF R f) p (data x E N) ≐ sample R f p x E N := by
  let X := data x E N
  have raw : Γ ⊢[PRAAx] ap2 (nameF R f) p X ≐ sample R f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF, ap2] using
      toPR_eq (Γ := Γ) (sample R f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample R f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,E,N])
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa using fields)

theorem frozen_variation (R : RationalMap) (f g : PR 2) (r t x y E N A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 f r x) (ap2 g t y) A D) : Γ ⊢[PRAAx]
    distanceBounded (frozen R f r x N) (frozen R g t y N) (R.gain E N*A) D := by
  have h1 := fraction_recode _ E (source_at f r x E hf)
  have h2 := fraction_recode _ E (source_at g t y E hg)
  exact R.variation _ _ _ _ E N A D (encoded_source f r x E hf) (encoded_source g t y E hg) hD
    (distance_congr h1.eqSymm h2.eqSymm (.eqRefl _) (.eqRefl _) (recode_distance_bound _ _ _ _ hD h))

theorem late_observations (R : RationalMap) (f g : PR 2) (p q r t x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (clock R p E N) r) (ht : Γ ⊢[PRAAx] le (clock R q E N) t) : Γ ⊢[PRAAx]
    distanceBounded (frozen R f r x N) (frozen R g t y N) (unit p+unit q) (unit p*unit q) := by
  let A := R.gain E N
  have cap₁ := le_trans (query_budget (Γ := Γ) A p) (unit_monotone hr)
  have cap₂ := le_trans (query_budget (Γ := Γ) A q) (unit_monotone ht)
  have hrD := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive t)
  have hpD := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  exact distance_radius_mono _ _ _ _ _ _ hrD hpD
    (by dsimp only [A] at cap₁ cap₂ ⊢
        ipra_le 𝔞(unit q)*𝔞(unit t)*sl cap₁+𝔞(unit p)*𝔞(unit r)*sl cap₂)
    (frozen_variation R f g r t x y E N _ _ hf hg hrD (cross_at f g x y r t he))

theorem proper (R : RationalMap) (f g : PR 2) (x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E) (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF R f) (nameF R g) (data x E N) (data y E N) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have ht : Δ ⊢[PRAAx] source g (sh y) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have hei : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have h := late_observations R f g p q (clock R p (sh E) (sh N)) (clock R q (sh E) (sh N))
    (sh x) (sh y) (sh E) (sh N) hs ht hei (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ] using
    distance_congr (sample_at R f p (sh x) (sh E) (sh N)).eqSymm
      (sample_at R g q (sh y) (sh E) (sh N)).eqSymm (.eqRefl _) (.eqRefl _) h

theorem name_regular (R : RationalMap) (f : PR 2) (x E N : PTm n) (hf : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF R f) (data x E N) :=
  proper R f f x x E N hf hf (cross_refl f x hf.andE₁)

theorem original_frozen_rate (R : RationalMap) (f : PR 2) (s k x E N : PTm n)
    (h : Γ ⊢[PRAAx] source f x E) (late : Γ ⊢[PRAAx] le (clock R s E N) k) :
    Γ ⊢[PRAAx] independentRate (nameF R f) constantF (data x E N) (frozen R f k x N) one (unit s) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let S := unit (sh s)
  let P := unit p
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  have hk : Δ ⊢[PRAAx] le (clock R (sh s) (sh E) (sh N)) (sh k) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using late.shift.shift
  have hl := late_observations R f f p (sh s) (clock R p (sh E) (sh N)) (sh k) (sh x) (sh x) (sh E) (sh N)
    hs hs (cross_refl f (sh x) hs.andE₁) (le_refl _) hk
  have mono : Δ ⊢[PRAAx] le ((P+S)*rateDenominator S p q) (rateNumerator one S p q*(P*S)) := by
    unfold rateNumerator rateDenominator
    dsimp only [P,S]
    ipra_le Groth.ι (Q.mk Δ (unit (sh s)))^2*Groth.ι (Q.mk Δ (unit p))^2
  have near := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive (sh s)))
    (denominator_positive _ _ _ (unit_positive (sh s))) mono hl
  simpa only [independentRate, subst_data, subst_frozen, GaussianCoefficientNameBounds.subst_unit, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift, sh, p, q, S, Δ] using
    distance_congr (sample_at R f p (sh x) (sh E) (sh N)).eqSymm (constant_at q (frozen R f (sh k) (sh x) (sh N))).eqSymm
      (.eqRefl _) (.eqRefl _) near

theorem actual_named_unit_interval_rational_extension_closed (R : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) ⟶ le (clock R (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF R f) constantF (data (var 0) (var 1) (var 2)) (frozen R f (var 4) (var 0) (var 2))
          one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (original_frozen_rate R f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedUnitIntervalRationalLift
