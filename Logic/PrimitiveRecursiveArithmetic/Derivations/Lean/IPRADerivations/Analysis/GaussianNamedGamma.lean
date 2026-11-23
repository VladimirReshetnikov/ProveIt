import IPRADerivations.Analysis.GaussianGammaHalfPlaneInputContinuity
import IPRADerivations.Analysis.GaussianNamedRightHalfPlane
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Analysis.GaussianExponentialReference

/-!
# A regular Gamma program on a fixed primitive-recursive complex name

The only source hypotheses are regularity of the input name and its
positive real margin. The output program evaluates the existing
encoded-rational Gamma at decoded observations of that same name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaHalfPlaneInputContinuity (modulus subst_modulus original_gamma_observations)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedRightHalfPlane (source threshold radius numerator denominator actual_late_source)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def demandBody : PTm 2 := modulus (var 0) (fstT (var 1)) (two*sndT (var 1))

/-- The finite maximum includes every comparison demand up to the current
output precision plus one. The real margin is available at this clock. -/
def clock (f : PR 2) (p x A : PTm n) : PTm n :=
  threshold A+succ (finiteMaximum demandBody (succ (succ p)) (pairT (radius f x) A))

def point (f : PR 2) (x r : PTm n) : PTm n :=
  ofGaussian (numerator f r x) (denominator f r x)

def sample (f : PR 2) (p x A : PTm n) : PTm n :=
  ap2 gammaF (succ p) (gammaData (numerator f (clock f p x A) x) (radius f x)
    (denominator f (clock f p x A) x) (two*A))

def data (x A : PTm n) : PTm n := pairT x A
def body (f : PR 2) : PTm 2 := sample f (var 0) (fstT (var 1)) (sndT (var 1))
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x A : PTm n) :
    Syn.subst σ (clock f p x A) = clock f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) := by
  simp [clock]

@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x A : PTm n) :
    Syn.subst σ (sample f p x A) = sample f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ A) := by
  simp [sample]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x A : PTm n) :
    Syn.subst σ (data x A) = data (Syn.subst σ x) (Syn.subst σ A) := by simp [data]

private theorem demand_at (s R A : PTm n) :
    Γ ⊢[PRAAx] inst2 demandBody s (pairT R A) ≐ modulus s R (two*A) := by
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (modulus (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![s, fstT (pairT R A), two*sndT (pairT R A)]) (σ' := ![s,R,two*A])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _
                 exact congrMul (.eqRefl two) (snd_pair _ _))
  simpa only [demandBody,inst2,subst_modulus,Syn.subst_var,subst_fstT,subst_sndT,PTm.subst_mul,
    PTm.subst_succ,PTm.subst_zero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using h

theorem clock_margin (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] le (threshold A) (clock f p x A) :=
  le_add_right _ _

theorem clock_demand (f : PR 2) (p x A s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A))) (clock f p x A) := by
  have hs' : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have maximum := le_congr (demand_at s (radius f x) A) (.eqRefl _)
    (finiteMaximum_at demandBody hs')
  have next := le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm
    (add_le_add_right one maximum)
  exact le_trans next (le_add_left _ _)

private theorem input_budget (r t m : PTm n)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t) :
    Γ ⊢[PRAAx] le ((unit r+unit t)*unit m) (one*(unit r*unit t)) := by
  have double : Γ ⊢[PRAAx] unit (succ m) ≐ two*unit m := (pw_succ two m).eqTrans (mul_comm _ _)
  have left := mul_le_mul_right (unit t) (le_congr double (.eqRefl _) (unit_monotone hr))
  have right := mul_le_mul_right (unit r) (le_congr double (.eqRefl _) (unit_monotone ht))
  have sum := add_le_add₂ left right
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) sum)

theorem input_observations (f : PR 2) (x r t m : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t) :
    Γ ⊢[PRAAx] distanceBounded (point f x r) (point f x t) one (unit m) := by
  have den := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive t)
  have obs := GaussianNameEquivalence.point_at f x r t h
  exact distance_radius_mono _ _ _ _ _ _ den (unit_positive m) (input_budget r t m hr ht)
    (GaussianFastValueCut.recode_distance_bound _ _ _ _ den obs)

private theorem output_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq)
    (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

private theorem observations_of_le (f : PR 2) (p q x A : PTm n)
    (h : Γ ⊢[PRAAx] source f x A) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x A) (sample f q x A) (unit p+unit q) (unit p*unit q) := by
  let r := clock f p x A
  let t := clock f q x A
  let R := radius f x
  let s := succ p
  let m := modulus s R (two*A)
  have hs : Γ ⊢[PRAAx] le s (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have hd : Γ ⊢[PRAAx] distanceBounded (point f x r) (point f x t) one (unit m) :=
    input_observations f x r t m h.andE₁ (clock_demand f p x A s (le_refl _)) (clock_demand f q x A s hs)
  have hR : Γ ⊢[PRAAx] le one R := GaussianNameBounds.U_positive f x
  have left := actual_late_source f x A r h (clock_margin f p x A)
  have right := actual_late_source f x A t h (clock_margin f q x A)
  have obs := original_gamma_observations (succ p) (succ q) s (numerator f r x) (numerator f t x)
    R (denominator f r x) (denominator f t x) (two*A) (.andI left hR) (.andI right hR) hd
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive s))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q) obs

theorem sample_observations (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x A) (sample f q x A) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le f p q x A h.wk Prf.hyp0) ?_
  have obs := observations_of_le f q p x A h.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) obs)

theorem name_at (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x A) ≐ sample f p x A := by
  have h : Γ ⊢[PRAAx] ap2 (nameF f) p (data x A) ≐ sample f p (fstT (data x A)) (sndT (data x A)) := by
    simpa only [nameF,body,ap2,subst_sample,Syn.subst_var,subst_fstT,subst_sndT,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (body f) ![p,data x A]
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![p,fstT (data x A),sndT (data x A)]) (σ' := ![p,x,A])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  exact h.eqTrans (by simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using eq)

theorem name_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x A) := by
  refine .allI (.allI ?_)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) := by
    simpa only [Fm.shift,GaussianNamedRightHalfPlane.subst_source,Syn.shift] using h.shift.shift
  simpa only [Syn.shift,subst_data,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (name_at f (var 1) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A))).eqSymm
      (name_at f (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A))).eqSymm
      (.eqRefl _) (.eqRefl _) (sample_observations f (var 1) (var 0) _ _ h')

theorem original_gamma_regular_at_named_half_plane_input_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

theorem original_gamma_at_named_input_program_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap2 (nameF f) (var 0) (data (var 1) (var 2)) ≐ sample f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (name_at f _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedGamma
