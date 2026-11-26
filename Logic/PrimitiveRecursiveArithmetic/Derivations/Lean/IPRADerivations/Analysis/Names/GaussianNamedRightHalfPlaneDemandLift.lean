import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneLift
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# Extend a uniformly continuous rational name to the right half-plane

Each output precision has a finite input demand on a certified margin
and disk. The maximum of the demands through the desired precision
supports comparisons between different output clocks. The actual inputs
to the rational evaluator are the late signed samples of the given name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneDemandLift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedRightHalfPlane (threshold)
open GaussianNamedRightHalfPlaneLift (source data late_certificate subst_source subst_data)
open GaussianNamedRightHalfPlaneSigned (certificate point point_distance)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

structure RationalMap where
  evaluator : PR 2
  rationalData : PR 3
  demand : PR 3
  variation : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (x y R K s : PTm m),
    (Δ ⊢[PRAAx] certificate x R K) → (Δ ⊢[PRAAx] certificate y R K) →
    (Δ ⊢[PRAAx] distanceBounded (point x) (point y) one (unit (ap3 demand s R K))) →
    (Δ ⊢[PRAAx] independentRate evaluator evaluator (ap3 rationalData x R K) (ap3 rationalData y R K) one (unit s))

def demandBody (map : RationalMap) : PTm 2 :=
  ap3 map.demand (var 0) (fstT (var 1)) (sndT (var 1))

def clock (map : RationalMap) (p M R : PTm n) : PTm n :=
  threshold M+succ (finiteMaximum (demandBody map) (succ (succ p)) (pairT R (two*M)))

def frozenData (map : RationalMap) (f : PR 2) (k x M R : PTm n) : PTm n :=
  ap3 map.rationalData (ap2 f k x) R (two*M)

def sample (map : RationalMap) (f : PR 2) (p x M R : PTm n) : PTm n :=
  ap2 map.evaluator (succ p) (frozenData map f (clock map p M R) x M R)

def nameF (map : RationalMap) (f : PR 2) : PR 2 := PTm.toPR
  (sample map f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (p M R : PTm n) :
    Syn.subst σ (clock map p M R) = clock map (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ R) := by
  simp [clock,two]

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (f : PR 2)
    (k x M R : PTm n) : Syn.subst σ (frozenData map f k x M R) =
      frozenData map f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ R) := by
  simp [frozenData,two]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (map : RationalMap) (f : PR 2)
    (p x M R : PTm n) : Syn.subst σ (sample map f p x M R) =
      sample map f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ R) := by
  simp [sample]

theorem sample_at (map : RationalMap) (f : PR 2) (p x M R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF map f) p (data x M R) ≐ sample map f p x M R := by
  let X := data x M R
  have raw : Γ ⊢[PRAAx] ap2 (nameF map f) p X ≐ sample map f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa [nameF,ap2] using
      toPR_eq (Γ := Γ)
        (sample map f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have e1 : Γ ⊢[PRAAx] fstT X ≐ x := fst_pair _ _
  have e2 : Γ ⊢[PRAAx] fstT (sndT X) ≐ M := (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
  have e3 : Γ ⊢[PRAAx] sndT (sndT X) ≐ R := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  refine raw.eqTrans ?_
  ipra_congr (sample map f (var 0) (var 1) (var 2) (var 3) : PTm 4) with [Prf.eqRefl p,e1,e2,e3]

private theorem demand_at (map : RationalMap) (s R K : PTm n) :
    Γ ⊢[PRAAx] inst2 (demandBody map) s (pairT R K) ≐ ap3 map.demand s R K := by
  simp only [demandBody,inst2,Syn.subst_var,subst_ap3,subst_fstT,subst_sndT]
  change Γ ⊢[PRAAx] ap3 map.demand s (fstT (pairT R K)) (sndT (pairT R K)) ≐ ap3 map.demand s R K
  ipra_congr (ap3 map.demand (var 0) (var 1) (var 2) : PTm 3) with [Prf.eqRefl s, fst_pair R K, snd_pair R K]

theorem clock_margin (map : RationalMap) (p M R : PTm n) : Γ ⊢[PRAAx] le (threshold M) (clock map p M R) :=
  le_add_right _ _

theorem clock_demand (map : RationalMap) (p M R s : PTm n) (h : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (ap3 map.demand s R (two*M))) (clock map p M R) := by
  have hs : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans h
  have maximum := le_congr (demand_at map s R (two*M)) (.eqRefl _)
    (finiteMaximum_at (demandBody map) hs)
  have next := le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
    (add_le_add_right one maximum)
  exact le_trans next (le_add_left _ _)

private theorem input_budget (r t m : PTm n)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t) :
    Γ ⊢[PRAAx] le ((unit r+unit t)*unit m) (one*(unit r*unit t)) := by
  have double : Γ ⊢[PRAAx] unit (succ m) ≐ two*unit m := (pw_succ two m).eqTrans (mul_comm _ _)
  have left := mul_le_mul_right (unit t) (le_congr double (.eqRefl _) (unit_monotone hr))
  have right := mul_le_mul_right (unit r) (le_congr double (.eqRefl _) (unit_monotone ht))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

theorem late_rate (map : RationalMap) (f g : PR 2) (s r t x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (threshold M) r) (ht : Γ ⊢[PRAAx] le (threshold M) t)
    (hd : Γ ⊢[PRAAx] le (succ (ap3 map.demand s R (two*M))) r)
    (he' : Γ ⊢[PRAAx] le (succ (ap3 map.demand s R (two*M))) t) :
    Γ ⊢[PRAAx] independentRate map.evaluator map.evaluator (frozenData map f r x M R) (frozenData map g t y M R)
      one (unit s) := by
  let m := ap3 map.demand s R (two*M)
  let U := unit r
  let V := unit t
  have left := late_certificate f x r M R hf hr
  have right := late_certificate g y t M R hg ht
  have den : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive r) (unit_positive t)
  have points := point_distance _ _ _ _ left.andE₁.andE₁.andE₁.andE₁ right.andE₁.andE₁.andE₁.andE₁ den
    (cross_at f g x y r t he)
  exact map.variation _ _ R (two*M) s left right
    (distance_radius_mono _ _ _ _ _ _ den (unit_positive m) (input_budget r t m hd he') points)

private theorem output_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

private theorem observations_of_le (map : RationalMap) (f g : PR 2) (p q r t x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (clock map p M R) r) (ht : Γ ⊢[PRAAx] le (clock map q M R) t)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 map.evaluator (succ p) (frozenData map f r x M R))
      (ap2 map.evaluator (succ q) (frozenData map g t y M R)) (unit p+unit q) (unit p*unit q) := by
  have hs : Γ ⊢[PRAAx] le (succ p) (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := late_rate map f g (succ p) r t x y M R hf hg he
    (le_trans (clock_margin map p M R) hr) (le_trans (clock_margin map q M R) ht)
    (le_trans (clock_demand map p M R (succ p) (le_refl _)) hr)
    (le_trans (clock_demand map q M R (succ p) hs) ht)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive (succ p)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q)
    (rate_at _ _ _ _ _ _ (succ p) (succ q) rate)

theorem late_observations (map : RationalMap) (f g : PR 2) (p q r t x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (clock map p M R) r) (ht : Γ ⊢[PRAAx] le (clock map q M R) t) :
    Γ ⊢[PRAAx] distanceBounded (ap2 map.evaluator (succ p) (frozenData map f r x M R))
      (ap2 map.evaluator (succ q) (frozenData map g t y M R)) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le map f g p q r t x y M R hf.wk hg.wk he.wk hr.wk ht.wk Prf.hyp0) ?_
  have observation := observations_of_le map g f q p t r y x M R hg.wk hf.wk
    (cross_symm _ _ _ _ he.wk) ht.wk hr.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) observation)

theorem proper (map : RationalMap) (f g : PR 2) (x y M R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x M R) (hg : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF map f) (nameF map g) (data x M R) (data y M R) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have left : Δ ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have right : Δ ⊢[PRAAx] source g (sh y) (sh M) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hg.shift.shift
  have same : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  have observation := late_observations map f g p q (clock map p (sh M) (sh R)) (clock map q (sh M) (sh R))
    (sh x) (sh y) (sh M) (sh R) left right same (le_refl _) (le_refl _)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh,p,q,Δ,sample] using
    distance_congr (sample_at map f p (sh x) (sh M) (sh R)).eqSymm
      (sample_at map g q (sh y) (sh M) (sh R)).eqSymm (.eqRefl _) (.eqRefl _) observation

theorem name_regular (map : RationalMap) (f : PR 2) (x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) : Γ ⊢[PRAAx] pointCN (nameF map f) (data x M R) :=
  proper map f f x x M R h h (cross_refl f x h.andE₁.andE₁)

theorem actual_named_right_half_plane_demand_extension_closed (map : RationalMap) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF map f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular map f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneDemandLift
