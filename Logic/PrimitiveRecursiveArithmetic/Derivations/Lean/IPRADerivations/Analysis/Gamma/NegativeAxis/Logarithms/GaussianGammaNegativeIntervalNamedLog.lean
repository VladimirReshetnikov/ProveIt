import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalNamedLogVariation
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianNamedEulerUnitTime
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# The original negative log-Gamma at a named offset

The actual observation is a rational log-absolute Gamma observation
at the fraction decoded from the original input name. A finite
maximum pays for all comparison precisions up to the output clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLog

open_ipra
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeIntervalNamedLogVariation (modulus rational_rate)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_refl)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)
open GaussianExponentialReference (unit_monotone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData

abbrev source (f : PR 2) (x E : PTm n) : Fm PTm n := GaussianNamedEulerUnitTime.source f x E

def demandBody : PTm 2 := modulus (var 0) (fstT (var 1)) (sndT (var 1))
def clock (p E N : PTm n) : PTm n := succ (finiteMaximum demandBody (succ (succ p)) (pairT E N))
def encodedData (f : PR 2) (k x N : PTm n) : PTm n :=
  ld (numerator (ap2 f k x)) (denominator (ap2 f k x)) N
def sample (f : PR 2) (p x E N : PTm n) : PTm n := ap2 L (succ p) (encodedData f (clock p E N) x N)
def data (x E N : PTm n) : PTm n := pairT x (pairT E N)
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))))

ipra_subst clock
ipra_subst encodedData
ipra_subst sample
ipra_subst data

private theorem demand_at (s E N : PTm n) : Γ ⊢[PRAAx] inst2 demandBody s (pairT E N) ≐ modulus s E N := by
  have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (modulus (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![s,fstT (pairT E N),sndT (pairT E N)]) (σ' := ![s,E,N])
    (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)
  simpa only [demandBody,inst2,GaussianGammaNegativeIntervalNamedLogVariation.subst_modulus,Syn.subst_var,
    subst_fstT,subst_sndT,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

theorem clock_demand (p E N s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (modulus s E N)) (clock p E N) := by
  have hs' : Γ ⊢[PRAAx] lt s (succ (succ p)) := (succ_monus_succ _ _).eqTrans hs
  have below := le_congr (demand_at s E N) (.eqRefl _) (finiteMaximum_at demandBody hs')
  exact le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one below)

theorem name_at (f : PR 2) (p x E N : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x E N) ≐ sample f p x E N := by
  let X := data x E N
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p X ≐ sample f p (fstT X) (fstT (sndT X)) (sndT (sndT X)) := by
    simpa only [nameF,ap2,subst_sample,Syn.subst_var,subst_fstT,subst_sndT,Matrix.cons_val_zero,Matrix.cons_val_one]
      using toPR_eq (Γ := Γ)
        (sample f (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,X]
  have fields := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (sample f (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![p,fstT X,fstT (sndT X),sndT (sndT X)]) (σ' := ![p,x,E,N])
    (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact raw.eqTrans (by simpa only [subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using fields)

theorem encoded_regular (f : PR 2) (k x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN L (encodedData f k x N) :=
  GaussianGammaNegativeIntervalLogAbsolute.name_regular _ _ N (GaussianNamedEulerUnitTime.encoded_source f k x E h).andE₁

private theorem input_budget (r t m : PTm n)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t) :
    Γ ⊢[PRAAx] le ((unit r+unit t)*unit m) (one*(unit r*unit t)) := by
  have double : Γ ⊢[PRAAx] unit (succ m) ≐ two*unit m := (pw_succ two m).eqTrans (mul_comm _ _)
  have left := mul_le_mul_right (unit t) (le_congr double (.eqRefl _) (unit_monotone hr))
  have right := mul_le_mul_right (unit r) (le_congr double (.eqRefl _) (unit_monotone ht))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

theorem encoded_rate (f g : PR 2) (r t s x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hr : Γ ⊢[PRAAx] le (succ (modulus s E N)) r) (ht : Γ ⊢[PRAAx] le (succ (modulus s E N)) t) :
    Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate L L
      (encodedData f r x N) (encodedData g t y N) one (unit s) := by
  let u := ap2 f r x
  let v := ap2 g t y
  let m := modulus s E N
  have hu := GaussianNamedEulerUnitTime.source_at f r x E hf
  have hv := GaussianNamedEulerUnitTime.source_at g t y E hg
  have den := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive t)
  have decoded := distance_congr (fraction_recode u E hu).eqSymm (fraction_recode v E hv).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianFastValueCut.recode_distance_bound _ _ _ _ den (cross_at f g x y r t he))
  have near := distance_radius_mono _ _ _ _ _ _ den (unit_positive m) (input_budget r t m hr ht) decoded
  exact rational_rate s _ _ _ _ E N
    (GaussianNamedEulerUnitTime.encoded_source f r x E hf) (GaussianNamedEulerUnitTime.encoded_source g t y E hg) near

private theorem output_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

private theorem observations_of_le (f g : PR 2) (p q x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (sample f p x E N) (sample g q y E N) (unit p+unit q) (unit p*unit q) := by
  let r := clock p E N
  let t := clock q E N
  let s := succ p
  have hs : Γ ⊢[PRAAx] le s (succ q) :=
    le_congr (succ_eq_add_one _).eqSymm (succ_eq_add_one _).eqSymm (add_le_add_right one hpq)
  have rate := encoded_rate f g r t s x y E N hf hg he
    (clock_demand p E N s (le_refl _)) (clock_demand q E N s hs)
  have obs := rate_at L L (encodedData f r x N) (encodedData g t y N) one (unit s) (succ p) (succ q) rate
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive s))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (output_budget p q) obs

theorem original_observations (f g : PR 2) (p q x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E N)) (ap2 (nameF g) q (data y E N))
      (unit p+unit q) (unit p*unit q) := by
  have sourceResult : Γ ⊢[PRAAx] distanceBounded (sample f p x E N) (sample g q y E N)
      (unit p+unit q) (unit p*unit q) := by
    refine .orE (le_total p q) (observations_of_le f g p q x y E N hf.wk hg.wk he.wk Prf.hyp0) ?_
    have back := observations_of_le g f q p y x E N hg.wk hf.wk (cross_symm _ _ _ _ he.wk) Prf.hyp0
    have den : (le q p)::Γ ⊢[PRAAx] le one (unit q*unit p) :=
      positive_product _ _ (unit_positive q) (unit_positive p)
    exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (distance_symmetric _ _ _ _ den back)
  exact distance_congr (name_at f p x E N).eqSymm (name_at g q y E N).eqSymm (.eqRefl _) (.eqRefl _) sourceResult

theorem proper (f g : PR 2) (x y E N : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x E N) (data y E N) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have sf : Δ ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Δ,sh,source,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hf.shift.shift
  have sg : Δ ⊢[PRAAx] source g (sh y) (sh E) := by
    simpa only [Δ,sh,source,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hg.shift.shift
  have se : Δ ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) := by simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh N) sf sg se

theorem name_regular (f : PR 2) (x E N : PTm n) (h : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x E N) := by
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,crossEquivalent] using
    proper f f x x E N h h (cross_refl f x h.andE₁)

theorem name_real (f : PR 2) (x E N : PTm n) : Γ ⊢[PRAAx] realSamples (nameF f) (data x E N) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let H := Syn.shift E
  let J := Syn.shift N
  let p : PTm (n+1) := var 0
  let a := numerator (ap2 f (clock p H J) X)
  let b := denominator (ap2 f (clock p H J) X)
  have h := real_sample_at L (ld a b J) (succ p) (GaussianGammaNegativeIntervalLogAbsolute.name_real (Γ := Δ) a b J)
  have e := name_at (Γ := Δ) f p X H J
  simpa only [realSamples,subst_data,Δ,X,H,J,p,Syn.shift] using
    Prf.andI (GaussianRationalHorner.canonical_congr e h.andE₁)
      (RationalGaussianEmbedding.axis_congr e.eqSymm h.andE₂)

theorem actual_named_negative_log_gamma_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶
        pointCN (nameF f) (data (var 0) (var 1) (var 2)) ⋏ realSamples (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.andI (name_regular f _ _ _ Prf.hyp0) (name_real f _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedLog
