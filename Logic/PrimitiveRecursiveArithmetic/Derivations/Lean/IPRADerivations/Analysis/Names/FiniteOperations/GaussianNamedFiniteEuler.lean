import IPRADerivations.Analysis.Beta.Endpoints.GaussianBetaAllDegreeMixedInverseContinuity
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGamma
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Actual finite Euler reciprocal on a fixed regular complex name

The positive real margin is transferred to decoded original observations
at a computed late clock. A finite maximum pays every earlier continuity
demand. The sampler uses the same all-degree certified reciprocal data
and its original finite Q_N program. All numerical degrees are internal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteEuler

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianBetaAllDegreeInverseContinuity (gain)
open GaussianNamedRightHalfPlane (threshold radius numerator denominator actual_late_source)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PR 2) (x A N : PTm n) : Fm PTm n := GaussianNamedRightHalfPlane.source f x A ⋏ le one N
def modulus (s R A N : PTm n) : PTm n := GaussianFastValueCut.exponent (gain R A N) s
def demandBody : PTm 2 := modulus (var 0) (fstT (var 1)) (two*fstT (sndT (var 1))) (sndT (sndT (var 1)))
def parameters (R A N : PTm n) : PTm n := pairT R (pairT A N)
def clock (f : PR 2) (p x A N : PTm n) : PTm n := threshold A+
  succ (finiteMaximum demandBody (succ (succ p)) (parameters (radius f x) A N))
def sample (f : PR 2) (p x A N : PTm n) : PTm n :=
  ap2 GaussianBetaAllDegreeEulerInverse.nameF (succ p)
    (GaussianBetaAllDegreeEulerInverse.data (numerator f (clock f p x A N) x)
      (denominator f (clock f p x A N) x) N)
def data (x A N : PTm n) : PTm n := pairT x (pairT A N)
def body (f : PR 2) : PTm 2 := sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def nameF (f : PR 2) : PR 2 := PTm.toPR (body f)
ipra_subst source
ipra_subst modulus
ipra_subst parameters
ipra_subst clock
ipra_subst sample
ipra_subst data

/-- The old numerical query budget spends the actual finite inverse gain. -/
theorem modulus_budget (s R A N : PTm n) : Γ ⊢[PRAAx] le (gain R A N*unit s) (unit (modulus s R A N)) :=
  GaussianFastValueCut.query_budget _ _

theorem encoded_observations (p q s z w R B C A N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianBetaAllDegreeEulerInverse.source z R B A N)
    (hw : Γ ⊢[PRAAx] GaussianBetaAllDegreeEulerInverse.source w R C A N)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianRationalHorner.ofGaussian z B) (GaussianRationalHorner.ofGaussian w C)
      one (unit (modulus s R A N))) : Γ ⊢[PRAAx]
    distanceBounded (ap2 GaussianBetaAllDegreeEulerInverse.nameF p (GaussianBetaAllDegreeEulerInverse.data z B N))
      (ap2 GaussianBetaAllDegreeEulerInverse.nameF q (GaussianBetaAllDegreeEulerInverse.data w C N))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  let U := unit (modulus s R A N)
  have old := GaussianBetaAllDegreeMixedInverseContinuity.original_observations p q z w R B C A one U N
    (.andI (.andI hz hw) (.andI (unit_positive _) hd))
  have compare := mul_le_mul_right (unit p*unit p*unit q*unit q) (modulus_budget (Γ := Γ) s R A N)
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive U p q (unit_positive _))
    (denominator_positive (unit s) p q (unit_positive s))
    (le_congr (by unfold rateNumerator rateDenominator; ipra_ring) (by unfold rateNumerator rateDenominator; ipra_ring)
      (add_le_add_right (U*(unit p+unit q)*(unit s)*(unit p*unit q)) compare)) old

private theorem demand_at (s R A N : PTm n) : Γ ⊢[PRAAx]
    inst2 demandBody s (parameters R A N) ≐ modulus s R (two*A) N := by
  have ra : Γ ⊢[PRAAx] fstT (parameters R A N) ≐ R := fst_pair _ _
  have aa : Γ ⊢[PRAAx] fstT (sndT (parameters R A N)) ≐ A := (snd_pair _ _).fstE
  have na : Γ ⊢[PRAAx] sndT (sndT (parameters R A N)) ≐ N := (snd_pair _ _).sndE
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (modulus (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![s,fstT (parameters R A N),two*fstT (sndT (parameters R A N)),sndT (sndT (parameters R A N))])
    (σ' := ![s,R,two*A,N])
    (fun i => by fin_cases i; exact .eqRefl _; exact ra; exact congrMul (.eqRefl two) aa; exact na)
  simpa only [demandBody,inst2,subst_modulus,Syn.subst_var,subst_fstT,subst_sndT,PTm.subst_mul,
    PTm.subst_succ,PTm.subst_zero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using h

theorem clock_margin (f : PR 2) (p x A N : PTm n) : Γ ⊢[PRAAx] le (threshold A) (clock f p x A N) := le_add_right _ _

theorem clock_demand (f : PR 2) (p x A N s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) : Γ ⊢[PRAAx]
    le (succ (modulus s (radius f x) (two*A) N)) (clock f p x A N) := by
  have hs' : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have maximum := le_congr (demand_at s (radius f x) A N) (.eqRefl _) (finiteMaximum_at demandBody hs')
  have next := le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one maximum)
  exact le_trans next (le_add_left _ _)

private theorem observations_of_le (f : PR 2) (p q x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (sample f p x A N) (sample f q x A N) (unit p+unit q) (unit p*unit q) := by
  let r := clock f p x A N
  let t := clock f q x A N
  let R := radius f x
  let s := succ p
  let m := modulus s R (two*A) N
  have hs : Γ ⊢[PRAAx] le s (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have hd := GaussianNamedGamma.input_observations f x r t m h.andE₁.andE₁
    (clock_demand f p x A N s (le_refl _)) (clock_demand f q x A N s hs)
  have left := actual_late_source f x A r h.andE₁ (clock_margin f p x A N)
  have right := actual_late_source f x A t h.andE₁ (clock_margin f q x A N)
  have obs := encoded_observations (succ p) (succ q) s (numerator f r x) (numerator f t x) R
    (denominator f r x) (denominator f t x) (two*A) N (.andI left h.andE₂) (.andI right h.andE₂) hd
  exact GaussianNamedRateRadius.distance_at_succ_clocks _ _ p q obs

theorem sample_observations (f : PR 2) (p q x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    distanceBounded (sample f p x A N) (sample f q x A N) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) (observations_of_le f p q x A N h.wk Prf.hyp0) ?_
  have obs := observations_of_le f q p x A N h.wk Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) obs)

theorem name_at (f : PR 2) (p x A N : PTm n) : Γ ⊢[PRAAx] ap2 (nameF f) p (data x A N) ≐ sample f p x A N := by
  have h : Γ ⊢[PRAAx] ap2 (nameF f) p (data x A N) ≐
      sample f p (fstT (data x A N)) (fstT (sndT (data x A N))) (sndT (sndT (data x A N))) := by
    simpa only [nameF,body,ap2,subst_sample,Syn.subst_var,subst_fstT,subst_sndT,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.tail_cons] using toPR_eq (Γ := Γ) (body f) ![p,data x A N]
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT (data x A N),fstT (sndT (data x A N)),sndT (sndT (data x A N))]) (σ' := ![p,x,A,N])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _
                 exact (snd_pair _ _).fstE
                 exact (snd_pair _ _).sndE)
  exact h.eqTrans (by simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using eq)

theorem name_regular (f : PR 2) (x A N : PTm n) (h : Γ ⊢[PRAAx] source f x A N) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data x A N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N)) := by
    simpa only [Fm.shift,subst_source,Syn.shift] using h.shift.shift
  simpa only [Syn.shift,subst_data,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (name_at f (var 1) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N))).eqSymm
      (name_at f (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift N))).eqSymm
      (.eqRefl _) (.eqRefl _) (sample_observations f (var 1) (var 0) _ _ _ hs)

/-- One late comparison step. The unrestricted independent-query binding
is derived separately using this actual regular sampler. -/
theorem late_step (f : PR 2) (p q s r x A N : PTm n)
    (h : Γ ⊢[PRAAx] source f x A N) (hs : Γ ⊢[PRAAx] le s (succ p))
    (hm : Γ ⊢[PRAAx] le (threshold A) r)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s (radius f x) (two*A) N)) r) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x A N))
      (ap2 GaussianBetaAllDegreeEulerInverse.nameF q (GaussianBetaAllDegreeEulerInverse.data (numerator f r x) (denominator f r x) N))
      (rateNumerator one (unit s) (succ p) q) (rateDenominator (unit s) (succ p) q) := by
  have hd := GaussianNamedGamma.input_observations f x (clock f p x A N) r (modulus s (radius f x) (two*A) N)
    h.andE₁.andE₁ (clock_demand f p x A N s hs) hr
  have left := actual_late_source f x A (clock f p x A N) h.andE₁ (clock_margin f p x A N)
  have right := actual_late_source f x A r h.andE₁ hm
  exact distance_congr (name_at f p x A N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (encoded_observations (succ p) q s _ _ _ _ _ _ N (.andI left h.andE₂) (.andI right h.andE₂) hd)

theorem actual_reciprocal_query (f : PR 2) (p x A N : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x A N) ≐ GaussianFastValueCut.recode
      (GaussianRationalReciprocal.reciprocal
        (ap2 GaussianGammaFiniteApproximantName.qF
          (GaussianBetaAllDegreeEulerInverse.query (succ p) (numerator f (clock f p x A N) x) (denominator f (clock f p x A N) x) N)
          (GaussianGammaFiniteApproximantName.qData (numerator f (clock f p x A N) x) (denominator f (clock f p x A N) x) N))) :=
  (name_at f p x A N).eqTrans (GaussianBetaAllDegreeEulerInverse.sample_literal _ _ _ _)

theorem original_named_finite_Euler_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))
theorem original_named_finite_Euler_program_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (nameF f) (var 0) (data (var 1) (var 2) (var 3)) ≐ sample f (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (name_at f _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteEuler
