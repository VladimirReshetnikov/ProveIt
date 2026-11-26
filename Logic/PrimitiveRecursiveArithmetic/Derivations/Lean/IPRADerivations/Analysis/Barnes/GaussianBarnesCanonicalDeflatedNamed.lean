import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDeflatedValueContinuity
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDeflatedValueUniformApartness
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalNamedDemand

/-!
# The original deflated Barnes coefficient on regular named inputs

At each output precision a finite input demand chooses an actual Gaussian
observation. The sampler evaluates the original rational deflated
coefficient there. Its separation on a certified half-unit neighborhood
comes from the same uniform rational certificate at the actual clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianBarnesCanonicalDeflatedValueContinuity (inputClock uniform_input)
open GaussianBarnesCanonicalNamedDemand (native_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNameReciprocal (apart anchor lower_congr)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open GaussianExponentialReference (unit_monotone)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalDeflatedValue.nameF
local notation "Vd" => GaussianBarnesCanonicalDeflatedValue.data

def source (f : PR 2) (x R m : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalNamedDemand.source f x R ⋏ le one m

def neighborhood (f : PR 2) (x m : PTm n) : Fm PTm n := .all
  (GaussianBarnesCanonicalDeflatedHead.neighborhood (rawGaussian (ap2 f (var 0) (Syn.shift x)))
    (rawDen (ap2 f (var 0) (Syn.shift x))) (Syn.shift m))

def data (x R m : PTm n) : PTm n := pairT x (pairT R m)
def demandBody : PTm 2 := inputClock (fstT (var 1)) (sndT (var 1)) (var 0)
def clock (p R m : PTm n) : PTm n := succ (finiteMaximum demandBody (succ (succ p)) (pairT R m))

def frozenData (f : PR 2) (k x R m : PTm n) : PTm n :=
  Vd (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) m

def sample (f : PR 2) (p x R m : PTm n) : PTm n := ap2 V (succ p) (frozenData f (clock p R m) x R m)

def nameF (f : PR 2) : PR 2 := PTm.toPR
  (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

def height (R m : PTm n) : PTm n := succ (GaussianBarnesCanonicalDeflatedValueUniformApartness.height R m)

@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x R m : PTm n) :
    (source f x R m).subst σ = source f (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by simp [source,one]

@[simp] theorem subst_neighborhood {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x m : PTm n) :
    (neighborhood f x m).subst σ = neighborhood f (Syn.subst σ x) (Syn.subst σ m) := by
  simp [neighborhood,Syn.shift_subst,Syn.subst_shift]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (x R m : PTm n) :
    Syn.subst σ (data x R m) = data (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by simp [data]

@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p R m : PTm n) :
    Syn.subst σ (clock p R m) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) := by simp [clock]

private theorem subst_coefficientData {l : ℕ} (σ : Fin n → PTm l) (z R B m : PTm n) :
    Syn.subst σ (Vd z R B m) = Vd (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [GaussianBarnesCanonicalDeflatedValue.data,GaussianBarnesCanonicalDeflatedValue.headCoefficientData,
    GaussianBarnesCanonicalDeflatedValue.outerData,GaussianBarnesCanonicalDeflatedValue.remainingLength,
    GaussianBarnesCanonicalDeflatedHead.data]

@[simp] theorem subst_frozenData {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (k x R m : PTm n) :
    Syn.subst σ (frozenData f k x R m) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by
  simp [frozenData,subst_coefficientData]

@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x R m : PTm n) :
    Syn.subst σ (sample f p x R m) = sample f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ R) (Syn.subst σ m) := by
  simp [sample]

theorem sample_at (f : PR 2) (p x R m : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p (data x R m) ≐ sample f p x R m := by
  let X := data x R m
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p X ≐ sample f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have first : Γ ⊢[PRAAx] fstT X ≐ x := fst_pair x (pairT R m)
  have rest : Γ ⊢[PRAAx] sndT X ≐ pairT R m := snd_pair x (pairT R m)
  refine raw.eqTrans ?_
  ipra_congr (sample f (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [.eqRefl p, first, (congrFst rest).eqTrans (fst_pair R m), (congrSnd rest).eqTrans (snd_pair R m)]

theorem rational_source (f : PR 2) (k x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalFactor.source (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x)) m := by
  have d := native_source f k x R h.andE₁
  exact .andI d.andE₁ (.andI h.andE₂ d.andE₂)

theorem neighborhood_at (f : PR 2) (k x m : PTm n) (h : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalDeflatedHead.neighborhood (rawGaussian (ap2 f k x)) (rawDen (ap2 f k x)) m := by
  simpa [neighborhood] using h.allE k

theorem clock_demand (p R m s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (inputClock R m s)) (clock p R m) := by
  let X := pairT R m
  have inside : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have read : Γ ⊢[PRAAx] inst2 demandBody s X ≐ inputClock R m s := by
    ipra_congr (inputClock (var 0) (var 1) (var 2) : PTm 3) with
      [fst_pair R m, snd_pair R m, .eqRefl s] using [demandBody,inst2,X]
  have raw := finiteMaximum_at demandBody (x := X) inside
  have top := le_congr read (.eqRefl _) raw
  exact le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one top)

private theorem input_budget (k l a : PTm n) (hk : Γ ⊢[PRAAx] le (succ a) k) (hl : Γ ⊢[PRAAx] le (succ a) l) :
    Γ ⊢[PRAAx] le ((unit k+unit l)*unit a) (one*(unit k*unit l)) := by
  have double : Γ ⊢[PRAAx] unit (succ a) ≐ two*unit a := (pw_succ two a).eqTrans (mul_comm _ _)
  have left := mul_le_mul_right (unit l) (le_congr double (.eqRefl _) (unit_monotone hk))
  have right := mul_le_mul_right (unit k) (le_congr double (.eqRefl _) (unit_monotone hl))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

theorem late_rate (f g : PR 2) (s k l x y R m : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R m) (hg : Γ ⊢[PRAAx] source g y R m)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (inputClock R m s)) k) (hl : Γ ⊢[PRAAx] le (succ (inputClock R m s)) l) :
    Γ ⊢[PRAAx] independentRate V V (frozenData f k x R m) (frozenData g l y R m) one (unit s) := by
  let a := inputClock R m s
  let q := ap2 f k x
  let r := ap2 g l y
  have den := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have recoded := GaussianFastValueCut.recode_distance_bound q r _ _ den (cross_at f g x y k l he)
  have fine := distance_radius_mono _ _ _ _ one (unit a) den (unit_positive a) (input_budget k l a hk hl) recoded
  exact uniform_input (rawGaussian q) (rawGaussian r) R (rawDen q) (rawDen r) m s
    (rational_source f k x R m hf) (rational_source g l y R m hg) fine

private theorem output_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

private theorem observations_of_le (f g : PR 2) (p q k l x y R m : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R m) (hg : Γ ⊢[PRAAx] source g y R m)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p R m) k) (hl : Γ ⊢[PRAAx] le (clock q R m) l)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R m)) (ap2 V (succ q) (frozenData g l y R m))
      (unit p+unit q) (unit p*unit q) := by
  have hs : Γ ⊢[PRAAx] le (succ p) (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := late_rate f g (succ p) k l x y R m hf hg he
    (le_trans (clock_demand p R m (succ p) (le_refl _)) hk)
    (le_trans (clock_demand q R m (succ p) hs) hl)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive (succ p)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q) (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem late_observations (f g : PR 2) (p q k l x y R m : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R m) (hg : Γ ⊢[PRAAx] source g y R m)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock p R m) k) (hl : Γ ⊢[PRAAx] le (clock q R m) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 V (succ p) (frozenData f k x R m)) (ap2 V (succ q) (frozenData g l y R m))
      (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le f g p q k l x y R m hf.wk hg.wk he.wk hk.wk hl.wk Prf.hyp0) ?_
  have rev := observations_of_le g f q p l k y x R m hg.wk hf.wk
    (cross_symm _ _ _ _ he.wk) hl.wk hk.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem proper (f g : PR 2) (x y R m : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R m) (hg : Γ ⊢[PRAAx] source g y R m)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R m) (data y R m) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh R) (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have obs := late_observations f g p q (clock p (sh R) (sh m)) (clock q (sh R) (sh m)) (sh x) (sh y) (sh R) (sh m)
    left right same (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ,sample] using
    distance_congr (sample_at f p (sh x) (sh R) (sh m)).eqSymm
      (sample_at g q (sh y) (sh R) (sh m)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem regular (f : PR 2) (x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x R m) :=
  proper f f x x R m h h (cross_refl f x h.andE₁.andE₁)

theorem original_apart (f : PR 2) (x R m : PTm n) (h : Γ ⊢[PRAAx] source f x R m)
    (hn : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] apart (nameF f) (height R m) (data x R m) := by
  let H := GaussianBarnesCanonicalDeflatedValueUniformApartness.height R m
  let p := anchor (height R m)
  let k := clock p R m
  let q := ap2 f k x
  have hP : Γ ⊢[PRAAx] le (anchor H) (succ p) :=
    le_trans (add_le_add_right two (le_succ_self H)) (le_succ_self p)
  have raw := GaussianBarnesCanonicalDeflatedValueUniformApartness.sample_lower (succ p)
    (rawGaussian q) R (rawDen q) m (rational_source f k x R m h) (neighborhood_at f k x m hn) hP
  exact lower_congr (sample_at f p x R m).eqSymm (.eqRefl _) raw

theorem actual_Barnes_deflated_named_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (regular f _ _ _ Prf.hyp0))

theorem actual_Barnes_deflated_named_uniform_apart_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((source f (var 0) (var 1) (var 2) ⋏ neighborhood f (var 0) (var 2)) ⟶
      apart (nameF f) (height (var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_apart f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedNamed
