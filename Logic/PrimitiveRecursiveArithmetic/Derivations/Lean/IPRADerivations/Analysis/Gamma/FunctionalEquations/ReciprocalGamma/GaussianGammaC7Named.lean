import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedDemand
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaHalfPlaneInputContinuity
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# The original entire reciprocal Gamma evaluator on regular Gaussian names

The disk modulus of the original C7 evaluator selects a finite read
of the input. Evaluate C7 on that observation's exact native rational
representation, at one extra bit of output accuracy.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7Named

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedRateRadius (distance_at_later_clocks distance_at_succ_clocks)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (distanceBounded bounded_iff)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianGammaC7Name.nameF
local notation "VD" => GaussianGammaC7Name.data
local notation "disk" => GaussianGammaCanonicalExponent.source
local notation "modulus" => GaussianGammaInputContinuity.modulus

def source (f : PR 2) (x R : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalNamedDemand.source f x R ⋏ le one R

abbrev data (x R : PTm n) : PTm n := GaussianBarnesCanonicalNamedDemand.data x R

def modulusF : PR 2 := PTm.toPR (modulus (var 0) (var 1) : PTm 2)

theorem modulus_at (s R : PTm n) : Γ ⊢[PRAAx] ap2 modulusF s R ≐ modulus s R := by
  have e := toPR_eq (Γ := Γ) (modulus (var 0) (var 1) : PTm 2) ![s,R]
  simpa [modulusF,ap2] using e

def demandBody : PTm 2 := ap2 modulusF (var 0) (var 1)

def clock (p R : PTm n) : PTm n :=
  succ (finiteMaximum demandBody (succ (succ p)) R)

def frozenData (f : PR 2) (k x R : PTm n) : PTm n :=
  VD (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x))

def sample (f : PR 2) (p x R : PTm n) : PTm n :=
  ap2 V (succ p) (frozenData f (clock p R) x R)

def nameF (f : PR 2) : PR 2 :=
  PTm.toPR (sample f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R : PTm n) :
    (source f x R).subst σ = source f (Syn.subst σ x) (Syn.subst σ R) := by simp [source,one]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x R : PTm n) :
    Syn.subst σ (data x R) = data (Syn.subst σ x) (Syn.subst σ R) := by simp [data]

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (clock p R) = clock (Syn.subst σ p) (Syn.subst σ R) := by simp [clock]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x R : PTm n) :
    Syn.subst σ (frozenData f k x R) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) := by simp [frozenData]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x R : PTm n) :
    Syn.subst σ (sample f p x R) = sample f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ R) := by simp [sample]

theorem sample_at (f : PR 2) (p x R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x R) ≐ sample f p x R := by
  let X := data x R
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p X ≐ sample f p (fstT X) (sndT X) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ) (sample f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,X]
  have first : Γ ⊢[PRAAx] fstT X ≐ x := fst_pair x R
  have second : Γ ⊢[PRAAx] sndT X ≐ R := snd_pair x R
  refine raw.eqTrans ?_
  ipra_congr (sample f (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl p, first, second]

theorem native_source (f : PR 2) (k x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] disk (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) :=
  .andI h.andE₂ (GaussianBarnesCanonicalNamedDemand.native_source f k x R h.andE₁)

theorem clock_demand (p R s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (ap2 modulusF s R)) (clock p R) := by
  have inside : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have top : Γ ⊢[PRAAx] le (ap2 modulusF s R) (finiteMaximum (demandBody) (succ (succ p)) R) :=
    by simpa [demandBody,inst2] using finiteMaximum_at (demandBody) (x := R) inside
  exact le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one top)

theorem late_rate (f g : PR 2) (s k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (ap2 modulusF s R)) k)
    (hl : Γ ⊢[PRAAx] le (succ (ap2 modulusF s R)) l) :
    Γ ⊢[PRAAx] independentRate V V (frozenData f k x R) (frozenData g l y R) one (unit s) := by
  let a := ap2 modulusF s R
  let q := ap2 f k x
  let r := ap2 g l y
  have den := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have recoded := GaussianFastValueCut.recode_distance_bound q r _ _ den (cross_at f g x y k l he)
  have fine := distance_at_later_clocks k l a hk hl recoded
  have budget : Γ ⊢[PRAAx] unit a ≐ unit (modulus s R) := by
    ipra_congr (unit (var 0) : PTm 1) with [modulus_at s R]
  exact GaussianGammaHalfPlaneInputContinuity.original_C7_mixed_rate s (rawGaussian q) (rawGaussian r) R
    (rawDen q) (rawDen r) (native_source f k x R hf) (native_source g l y R hg)
    (distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) budget fine)

private theorem observations_of_le (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p R) k) (hl : Γ ⊢[PRAAx] le (clock q R) l)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R)) (ap2 V (succ q) (frozenData g l y R))
      (unit p+unit q) (unit p*unit q) := by
  have hs : Γ ⊢[PRAAx] le (succ p) (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := late_rate f g (succ p) k l x y R hf hg he
    (le_trans (clock_demand p R (succ p) (le_refl _)) hk)
    (le_trans (clock_demand q R (succ p) hs) hl)
  exact distance_at_succ_clocks _ _ p q (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem late_observations (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p R) k) (hl : Γ ⊢[PRAAx] le (clock q R) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R)) (ap2 V (succ q) (frozenData g l y R))
      (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le f g p q k l x y R hf.wk hg.wk he.wk hk.wk hl.wk Prf.hyp0) ?_
  have rev := observations_of_le g f q p l k y x R hg.wk hf.wk
    (cross_symm _ _ _ _ he.wk) hl.wk hk.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem proper (f g : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R) (data y R) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have obs := late_observations f g p q (clock p (sh R)) (clock q (sh R)) (sh x) (sh y) (sh R)
    left right same (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ,sample] using
    distance_congr (sample_at f p (sh x) (sh R)).eqSymm
      (sample_at g q (sh y) (sh R)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem name_regular (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R) :=
  proper f f x x R h h (cross_refl f x h.andE₁.andE₁)

theorem actual_original_C7_named_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaC7Named
