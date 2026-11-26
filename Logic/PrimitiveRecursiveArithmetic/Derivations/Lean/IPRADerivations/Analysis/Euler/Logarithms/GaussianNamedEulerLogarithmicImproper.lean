import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianEulerLogarithmicMixedParameterRate
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGamma
import IPRADerivations.Foundations.DyadicGain

/-!
# The original logarithmic improper quadrature on a regular complex name

Each output is an observation of the original native logarithmic improper
program at one decoded observation of the input name. A finite maximum over
all earlier parameter demands gives a clock that is sufficient for any
comparison with an earlier output. The radius and positive margin are
those certified for the actual input name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicImproper

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_succ_bound)
open GaussianEulerLogarithmicContinuity (modulus subst_modulus)
open GaussianNamedRightHalfPlane (source threshold radius numerator denominator actual_late_source)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_of_ordered_observations)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "idata" => GaussianEulerLogarithmicImproperName.data

def outputPrecision (p : PTm n) : PTm n := p+num 3
def demandData (j R A : PTm n) : PTm n := pairT j (pairT R A)
def demandBody : PTm 2 := modulus (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (two*sndT (sndT (var 1)))
def clock (f : PR 2) (p j x A : PTm n) : PTm n :=
  threshold A+succ (finiteMaximum demandBody (succ (outputPrecision p)) (demandData j (radius f x) A))
def sample (f : PR 2) (p j x A : PTm n) : PTm n :=
  ap2 I (outputPrecision p) (idata j (numerator f (clock f p j x A) x) (radius f x)
    (denominator f (clock f p j x A) x) (two*A))
def data (j x A : PTm n) : PTm n := pairT j (pairT x A)
def body (f : PR 2) : PTm 2 := sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)

ipra_subst clock [outputPrecision, demandData]
ipra_subst sample [outputPrecision]
ipra_subst data

private theorem demand_at (s j R A : PTm n) : Γ ⊢[PRAAx]
    inst2 demandBody s (demandData j R A) ≐ modulus s j R (two*A) := by
  let d := demandData j R A
  have right := snd_pair (Γ := Γ) j (pairT R A)
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (modulus (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![s,fstT d,fstT (sndT d),two*sndT (sndT d)]) (σ' := ![s,j,R,two*A]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact right.fstE
      · exact congrMul (.eqRefl _) right.sndE)
  simpa only [inst2,demandBody,subst_modulus,Syn.subst_var,subst_fstT,subst_sndT,PTm.subst_mul,
    PTm.subst_succ,PTm.subst_zero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,d] using h

theorem clock_margin (f : PR 2) (p j x A : PTm n) :
    Γ ⊢[PRAAx] le (threshold A) (clock f p j x A) := le_add_right _ _

theorem clock_demand (f : PR 2) (p j x A s : PTm n) (h : Γ ⊢[PRAAx] le s (outputPrecision p)) :
    Γ ⊢[PRAAx] le (succ (modulus s j (radius f x) (two*A))) (clock f p j x A) := by
  exact le_trans (finiteMaximum_succ_bound demandBody h (demand_at s j (radius f x) A)) (le_add_left _ _)

private theorem output_unit (p : PTm n) : Γ ⊢[PRAAx] unit (outputPrecision p) ≐ num 8*unit p := by
  have eq : Γ ⊢[PRAAx] outputPrecision p ≐ succ (succ (succ p)) := by unfold outputPrecision; ipra_ring
  have stepped := (pw_succ (Γ := Γ) two (succ (succ p))).eqTrans
    (congrMul ((pw_succ two (succ p)).eqTrans
      (congrMul (pw_succ two p) (.eqRefl two))) (.eqRefl two))
  exact (congrAp2 powF eq (.eqRefl two)).eqTrans (stepped.eqTrans (by unfold unit; ipra_ring))

private theorem sample_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator (num 5) (unit (outputPrecision p)) (outputPrecision p) (outputPrecision q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (outputPrecision p)) (outputPrecision p) (outputPrecision q)) := by
  have dp := output_unit (Γ := Γ) p
  have dq := output_unit (Γ := Γ) q
  have dn := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl (num 5)) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) dn).eqSymm
    (le_of_eq_add (d := num 448*unit p*unit p*unit p*unit q+num 128*unit p*unit p*unit q*unit q) (by ipra_ring))

private theorem observations_of_le (f : PR 2) (p q j x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample f p j x A) (sample f q j x A) (unit p+unit q) (unit p*unit q) := by
  let r := clock f p j x A
  let t := clock f q j x A
  let R := radius f x
  let s := outputPrecision p
  let m := modulus s j R (two*A)
  have larger : Γ ⊢[PRAAx] le s (outputPrecision q) := add_le_add_right (num 3) hpq
  have close := GaussianNamedGamma.input_observations f x r t m h.andE₁
    (clock_demand f p j x A s (le_refl s)) (clock_demand f q j x A s larger)
  have near := distance_radius_mono _ _ one (unit m) one m (unit_positive m)
    (GaussianEulerLogarithmicContinuity.modulus_positive s j R (two*A))
    (le_congr (by ipra_ring) (by unfold unit; ipra_ring) (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb m)) close
  have left := actual_late_source f x A r h (clock_margin f p j x A)
  have right := actual_late_source f x A t h (clock_margin f q j x A)
  have cmp := GaussianEulerLogarithmicMixedParameterRate.original_mixed_parameter_rate s j
    (numerator f t x) (numerator f r x) R R (denominator f t x) (denominator f r x) (two*A) (two*A)
    (.andI right (.andI left near))
  have obs := rate_at I I _ _ (num 5) (unit s) (outputPrecision p) (outputPrecision q) cmp
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive s))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (sample_budget p q) obs

theorem original_observations (f : PR 2) (p q j x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (sample f p j x A) (sample f q j x A) (unit p+unit q) (unit p*unit q) := by
  exact distance_of_ordered_observations _ _ p q
    (observations_of_le f p q j x A h.wk Prf.hyp0)
    (observations_of_le f q p j x A h.wk Prf.hyp0)

theorem name_at (f : PR 2) (p j x A : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p (data j x A) ≐ sample f p j x A := by
  let d := data j x A
  have eval : Γ ⊢[PRAAx] ap2 (nameF f) p d ≐ sample f p (fstT d) (fstT (sndT d)) (sndT (sndT d)) := by
    simpa only [nameF,body,ap2,subst_sample,Syn.subst_var,subst_fstT,subst_sndT,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (body f) ![p,d]
  have last := snd_pair (Γ := Γ) j (pairT x A)
  have code := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT d,fstT (sndT d),sndT (sndT d)]) (σ' := ![p,j,x,A]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact last.fstE
      · exact last.sndE)
  exact eval.eqTrans (by simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using code)

theorem name_regular (f : PR 2) (j x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data j x A) := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh A) := by
    simpa only [Fm.shift,GaussianNamedRightHalfPlane.subst_source,Syn.shift,sh] using h.shift.shift
  simpa only [Syn.shift,subst_data,sh,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (name_at f (var 1) (sh j) (sh x) (sh A)).eqSymm (name_at f (var 0) (sh j) (sh x) (sh A)).eqSymm
      (.eqRefl _) (.eqRefl _) (original_observations f (var 1) (var 0) (sh j) (sh x) (sh A) h')

theorem actual_original_logarithmic_improper_regular_on_a_fixed_name_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicImproper
