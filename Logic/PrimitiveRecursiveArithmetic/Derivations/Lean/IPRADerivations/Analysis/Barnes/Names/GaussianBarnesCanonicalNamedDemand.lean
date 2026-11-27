import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalValue
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference
import IPRADerivations.Analysis.Names.Approximation.GaussianNameBounds
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Lift the original rational Barnes value to regular Gaussian names

A supplied rational continuity modulus determines a finite input
clock. The sampler uses the actual Gaussian observation at that clock
and the original rational Barnes evaluator at a separate output
precision. Each name needs only its Cauchy proof and a uniform disk
bound on its original observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedDemand

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_succ_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedRateRadius (distance_at_later_clocks distance_at_succ_clocks)
open GaussianRationalDistanceOrder (distance_congr distance_of_ordered_observations)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded bounded_iff)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "VD" => GaussianBarnesCanonicalValue.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

structure Modulus where
  inputClockF : PR 2
  uniform_input : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (z w R B D p : PTm m),
    (Δ ⊢[PRAAx] disk z R B) → (Δ ⊢[PRAAx] disk w R D) →
    (Δ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (ap2 inputClockF R p))) →
    (Δ ⊢[PRAAx] independentRate V V (VD z R B) (VD w R D) one (unit p))

def source (f : PR 2) (x R : PTm n) : Fm PTm n := pointCN f x ⋏ pointBounds f R x

def data (x R : PTm n) : PTm n := pairT x R

def demandBody (modulus : Modulus) : PTm 2 := ap2 modulus.inputClockF (var 1) (var 0)

def clock (modulus : Modulus) (p R : PTm n) : PTm n :=
  succ (finiteMaximum (demandBody modulus) (succ (succ p)) R)

def frozenData (f : PR 2) (k x R : PTm n) : PTm n :=
  VD (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x))

def sample (modulus : Modulus) (f : PR 2) (p x R : PTm n) : PTm n :=
  ap2 V (succ p) (frozenData f (clock modulus p R) x R)

def nameF (modulus : Modulus) (f : PR 2) : PR 2 :=
  PTm.toPR (sample modulus f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R : PTm n) :
    (source f x R).subst σ = source f (Syn.subst σ x) (Syn.subst σ R) := by simp [source]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x R : PTm n) :
    Syn.subst σ (data x R) = data (Syn.subst σ x) (Syn.subst σ R) := by simp [data]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (modulus : Modulus) (p R : PTm n) :
    Syn.subst σ (clock modulus p R) = clock modulus (Syn.subst σ p) (Syn.subst σ R) := by simp [clock]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x R : PTm n) :
    Syn.subst σ (frozenData f k x R) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) := by simp [frozenData]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (modulus : Modulus) (f : PR 2) (p x R : PTm n) :
    Syn.subst σ (sample modulus f p x R) = sample modulus f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ R) := by simp [sample]

theorem sample_at (modulus : Modulus) (f : PR 2) (p x R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF modulus f) p (data x R) ≐ sample modulus f p x R := by
  simpa [nameF, data] using
    (toPR_pair_eq (Γ := Γ) (sample modulus f (var 0) (var 1) (var 2)) p x R)

theorem source_of_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] source f x (GaussianNameBounds.U f x) :=
  .andI h (GaussianNameBounds.all_samples_bounded f x h)

theorem native_source (f : PR 2) (k x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] disk (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) := by
  let q := ap2 f k x
  have den := raw_den_positive (Γ := Γ) q
  have obs := GaussianRootApproximationWitness.point_at f R x k h.andE₂
  have norm := (bounded_iff q (rawGaussian q) (rawDen q) R one den (le_refl one) (raw_represents q)).iffMp obs
  exact .andI den (le_congr (by ipra_ring) (by ipra_ring) norm)

theorem clock_demand (modulus : Modulus) (p R s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) (clock modulus p R) := by
  exact finiteMaximum_succ_bound (demandBody modulus) (x := R) hs
    (by simp [demandBody,inst2] <;> exact .eqRefl _)

theorem late_rate (modulus : Modulus) (f g : PR 2) (s k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) k)
    (hl : Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) l) :
    Γ ⊢[PRAAx] independentRate V V (frozenData f k x R) (frozenData g l y R) one (unit s) := by
  let a := ap2 modulus.inputClockF R s
  let q := ap2 f k x
  let r := ap2 g l y
  have den := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have recoded := GaussianFastValueCut.recode_distance_bound q r _ _ den (cross_at f g x y k l he)
  have fine := distance_at_later_clocks k l a hk hl recoded
  exact modulus.uniform_input (rawGaussian q) (rawGaussian r) R (rawDen q) (rawDen r) s
    (native_source f k x R hf) (native_source g l y R hg) fine

private theorem observations_of_le (modulus : Modulus) (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock modulus p R) k) (hl : Γ ⊢[PRAAx] le (clock modulus q R) l)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R)) (ap2 V (succ q) (frozenData g l y R))
      (unit p+unit q) (unit p*unit q) := by
  have hs : Γ ⊢[PRAAx] le (succ p) (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := late_rate modulus f g (succ p) k l x y R hf hg he
    (le_trans (clock_demand modulus p R (succ p) (le_refl _)) hk)
    (le_trans (clock_demand modulus q R (succ p) hs) hl)
  exact distance_at_succ_clocks _ _ p q (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem late_observations (modulus : Modulus) (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock modulus p R) k) (hl : Γ ⊢[PRAAx] le (clock modulus q R) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R)) (ap2 V (succ q) (frozenData g l y R))
      (unit p+unit q) (unit p*unit q) := by
  exact distance_of_ordered_observations _ _ p q
    (observations_of_le modulus f g p q k l x y R hf.wk hg.wk he.wk hk.wk hl.wk Prf.hyp0)
    (observations_of_le modulus g f q p l k y x R hg.wk hf.wk
    (cross_symm _ _ _ _ he.wk) hl.wk hk.wk Prf.hyp0)

theorem proper (modulus : Modulus) (f g : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF modulus f) (nameF modulus g) (data x R) (data y R) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have obs := late_observations modulus f g p q (clock modulus p (sh R)) (clock modulus q (sh R)) (sh x) (sh y) (sh R)
    left right same (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ,sample] using
    distance_congr (sample_at modulus f p (sh x) (sh R)).eqSymm
      (sample_at modulus g q (sh y) (sh R)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem name_regular (modulus : Modulus) (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF modulus f) (data x R) :=
  proper modulus f f x x R h h (cross_refl f x h.andE₁)

theorem actual_Barnes_named_demand_regular_closed (modulus : Modulus) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF modulus f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular modulus f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedDemand
