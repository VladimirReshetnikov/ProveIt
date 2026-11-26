import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedDemand

/-!
# Demand lift of an executable rational map on a Gaussian disk

The sampler evaluates the rational map at a finite observation of the
original input name. A proved rational map controls the finite
query schedule and the regularity of these observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedDiskDemandLift

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open GaussianBarnesCanonicalNamedDemand (source data subst_data native_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

structure RationalMap where
  evaluator : PR 2
  rationalData : PTm 3
  inputClockF : PR 2
  uniform_input : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (z w R B D p : PTm m),
    (Δ ⊢[PRAAx] disk z R B) → (Δ ⊢[PRAAx] disk w R D) →
    (Δ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (ap2 inputClockF R p))) →
    (Δ ⊢[PRAAx] independentRate evaluator evaluator (inst3 rationalData z R B) (inst3 rationalData w R D) one (unit p))

def demandBody (map : RationalMap) : PTm 2 := ap2 map.inputClockF (var 1) (var 0)

def clock (map : RationalMap) (p R : PTm n) : PTm n :=
  succ (finiteMaximum (demandBody map) (succ (succ p)) R)

def frozenData (map : RationalMap) (f : PR 2) (k x R : PTm n) : PTm n :=
  inst3 map.rationalData (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x))

def sample (map : RationalMap) (f : PR 2) (p x R : PTm n) : PTm n :=
  ap2 map.evaluator (succ p) (frozenData map f (clock map p R) x R)

def nameF (map : RationalMap) (f : PR 2) : PR 2 :=
  PTm.toPR (sample map f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (p R : PTm n) :
    Syn.subst σ (clock map p R) = clock map (Syn.subst σ p) (Syn.subst σ R) := by simp [clock]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (f : PR 2) (k x R : PTm n) :
    Syn.subst σ (frozenData map f k x R) = frozenData map f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) := by simp [frozenData]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (f : PR 2) (p x R : PTm n) :
    Syn.subst σ (sample map f p x R) = sample map f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ R) := by simp [sample]

theorem sample_at (map : RationalMap) (f : PR 2) (p x R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF map f) p (data x R) ≐ sample map f p x R := by
  let X := data x R
  have raw : Γ ⊢[PRAAx] ap2 (nameF map f) p X ≐ sample map f p (fstT X) (sndT X) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ) (sample map f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,X]
  have first : Γ ⊢[PRAAx] fstT X ≐ x := fst_pair x R
  have second : Γ ⊢[PRAAx] sndT X ≐ R := snd_pair x R
  refine raw.eqTrans ?_
  ipra_congr (sample map f (var 0) (var 1) (var 2) : PTm 3) with
    [.eqRefl p, first, second]

theorem clock_demand (map : RationalMap) (p R s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (ap2 map.inputClockF R s)) (clock map p R) := by
  have inside : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have top : Γ ⊢[PRAAx] le (ap2 map.inputClockF R s) (finiteMaximum (demandBody map) (succ (succ p)) R) :=
    by simpa [demandBody,inst2] using finiteMaximum_at (demandBody map) (x := R) inside
  exact le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one top)

theorem input_budget (k l a : PTm n) (hk : Γ ⊢[PRAAx] le (succ a) k) (hl : Γ ⊢[PRAAx] le (succ a) l) :
    Γ ⊢[PRAAx] le ((unit k+unit l)*unit a) (one*(unit k*unit l)) := by
  have double : Γ ⊢[PRAAx] unit (succ a) ≐ two*unit a := (pw_succ two a).eqTrans (mul_comm _ _)
  have left := mul_le_mul_right (unit l) (le_congr double (.eqRefl _) (unit_monotone hk))
  have right := mul_le_mul_right (unit k) (le_congr double (.eqRefl _) (unit_monotone hl))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

theorem late_rate (map : RationalMap) (f g : PR 2) (s k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (ap2 map.inputClockF R s)) k)
    (hl : Γ ⊢[PRAAx] le (succ (ap2 map.inputClockF R s)) l) :
    Γ ⊢[PRAAx] independentRate map.evaluator map.evaluator (frozenData map f k x R) (frozenData map g l y R) one (unit s) := by
  let a := ap2 map.inputClockF R s
  let q := ap2 f k x
  let r := ap2 g l y
  have den := positive_product _ _ (unit_positive (Γ := Γ) k) (unit_positive l)
  have recoded := GaussianFastValueCut.recode_distance_bound q r _ _ den (cross_at f g x y k l he)
  have fine := distance_radius_mono _ _ _ _ one (unit a) den (unit_positive a) (input_budget k l a hk hl) recoded
  exact map.uniform_input (rawGaussian q) (rawGaussian r) R (rawDen q) (rawDen r) s
    (native_source f k x R hf) (native_source g l y R hg) fine

theorem output_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

private theorem observations_of_le (map : RationalMap) (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock map p R) k) (hl : Γ ⊢[PRAAx] le (clock map q R) l)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 map.evaluator (succ p) (frozenData map f k x R)) (ap2 map.evaluator (succ q) (frozenData map g l y R))
      (unit p+unit q) (unit p*unit q) := by
  have hs : Γ ⊢[PRAAx] le (succ p) (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := late_rate map f g (succ p) k l x y R hf hg he
    (le_trans (clock_demand map p R (succ p) (le_refl _)) hk)
    (le_trans (clock_demand map q R (succ p) hs) hl)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive (succ p)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q)
    (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem late_observations (map : RationalMap) (f g : PR 2) (p q k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (clock map p R) k) (hl : Γ ⊢[PRAAx] le (clock map q R) l) :
    Γ ⊢[PRAAx] distanceBounded (ap2 map.evaluator (succ p) (frozenData map f k x R)) (ap2 map.evaluator (succ q) (frozenData map g l y R))
      (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le map f g p q k l x y R hf.wk hg.wk he.wk hk.wk hl.wk Prf.hyp0) ?_
  have rev := observations_of_le map g f q p l k y x R hg.wk hf.wk
    (cross_symm _ _ _ _ he.wk) hl.wk hk.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) rev)

theorem proper (map : RationalMap) (f g : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF map f) (nameF map g) (data x R) (data y R) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have obs := late_observations map f g p q (clock map p (sh R)) (clock map q (sh R)) (sh x) (sh y) (sh R)
    left right same (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ,sample] using
    distance_congr (sample_at map f p (sh x) (sh R)).eqSymm
      (sample_at map g q (sh y) (sh R)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem name_regular (map : RationalMap) (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF map f) (data x R) :=
  proper map f f x x R h h (cross_refl f x h.andE₁)

theorem actual_named_disk_demand_regular_closed (map : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF map f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular map f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDiskDemandLift
