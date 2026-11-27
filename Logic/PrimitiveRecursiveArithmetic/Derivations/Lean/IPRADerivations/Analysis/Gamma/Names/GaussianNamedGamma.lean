import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaHalfPlaneInputContinuity
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlane
import IPRADerivations.Foundations.FiniteQueryDemand
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# A regular Gamma program on a fixed primitive-recursive complex name

The only source hypotheses are regularity of the input name and its
positive real margin. The output program evaluates the existing
encoded-rational Gamma at decoded observations of that same name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedGamma

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_succ_bound)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaHalfPlaneInputContinuity (modulus subst_modulus original_gamma_observations)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianNamedRightHalfPlane (source threshold radius numerator denominator actual_late_source)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianNamedRateRadius (distance_at_later_clocks distance_at_succ_clocks)
open GaussianRationalDistanceOrder (distance_congr distance_of_ordered_observations)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)

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

ipra_subst clock

ipra_subst sample

ipra_subst data

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
  exact le_trans (finiteMaximum_succ_bound demandBody hs (demand_at s (radius f x) A)) (le_add_left _ _)

theorem input_observations (f : PR 2) (x r t m : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t) :
    Γ ⊢[PRAAx] distanceBounded (point f x r) (point f x t) one (unit m) := by
  have den := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive t)
  have obs := GaussianNameEquivalence.point_at f x r t h
  exact distance_at_later_clocks r t m hr ht (GaussianFastValueCut.recode_distance_bound _ _ _ _ den obs)

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
  exact distance_at_succ_clocks _ _ p q obs

theorem sample_observations (f : PR 2) (p q x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x A) (sample f q x A) (unit p+unit q) (unit p*unit q) := by
  exact distance_of_ordered_observations _ _ p q
    (observations_of_le f p q x A h.wk Prf.hyp0)
    (observations_of_le f q p x A h.wk Prf.hyp0)

theorem name_at (f : PR 2) (p x A : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x A) ≐ sample f p x A := by
  simpa [nameF, body, data] using
    (toPR_pair_eq (Γ := Γ) (sample f (var 0) (var 1) (var 2)) p x A)

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
