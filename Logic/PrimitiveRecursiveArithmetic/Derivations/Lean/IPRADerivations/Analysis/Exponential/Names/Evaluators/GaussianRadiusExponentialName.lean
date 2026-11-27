import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalRadiusExponentialLipschitz
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianUnitDiskExponentialName

/-!
# Actual exponentiation of regular names on every fixed integer disk

The old scalarSum and old factorial-tail cutoff are unchanged. The
original input is observed at the computed precision
S_R(p)=p+4+(R+2)*lastIndex(R,p+4). Earlier-cutoff comparison uses the
real finite Lipschitz factor, whose binary bound is covered by S_R.
The later-cutoff error is the existing actual scalar exponential tail.
Thus the fixed PR2 output is genuinely regular from original pointCN
and original Euclidean radius-R samples, including R0/raw inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRadiusExponentialName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalExponentialTail (lastIndex precisionDenominator)
open GaussianRationalRadiusExponentialLipschitz (factor factor_binary_bound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def index (R p : PTm n) : PTm n := lastIndex R (p+num 4)
def inputPrecision (R p : PTm n) : PTm n := p+num 4+(R+two)*index R p
def query (f : PR 2) (R p x : PTm n) : PTm n := ap2 f (inputPrecision R p) x
def value (f : PR 2) (R p x : PTm n) : PTm n := scalarSum (query f R p x) (index R p)
def boundedSamples (f : PR 2) (R x : PTm n) : Fm PTm n := .all
  (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift R) one)
def input (f : PR 2) (R x : PTm n) : Fm PTm n := pointCN f x ⋏ boundedSamples f R x
def commonDenominator (p : PTm n) : PTm n := unit (succ p)
ipra_subst index
ipra_subst inputPrecision
ipra_subst query
ipra_subst value
ipra_subst boundedSamples [Syn.subst_shift, Syn.shift_subst]
ipra_subst input
ipra_subst commonDenominator

theorem bounded_samples_at (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] boundedSamples f R x) : Γ ⊢[PRAAx]
    bounded (ap2 f p x) R one := by simpa [boundedSamples] using h.allE p
theorem query_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx] bounded (query f R p x) R one :=
  bounded_samples_at f R x (inputPrecision R p) h.andE₂

theorem index_positive (R p : PTm n) : Γ ⊢[PRAAx] le one (index R p) := by
  have h : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff R (p+num 4)) :=
    le_of_eq_add (d := R+R+R*(R+R)+p+num 6) (by unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt; ipra_ring)
  exact (succ_monus_succ one (index R p)).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor R (p+num 4)).eqSymm h)

theorem index_add (R p k : PTm n) : Γ ⊢[PRAAx] index R (p+k) ≐ index R p+k := by
  have eq : Γ ⊢[PRAAx] succ (index R (p+k)) ≐ succ (index R p+k) :=
    (GaussianRationalExponentialTail.last_successor R (p+k+num 4)).eqTrans
      ((by unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt; ipra_ring :
        Γ ⊢[PRAAx] GaussianRationalExponentialTail.cutoff R (p+k+num 4) ≐
          GaussianRationalExponentialTail.cutoff R (p+num 4)+k).eqTrans
        ((congrAdd (GaussianRationalExponentialTail.last_successor R (p+num 4)).eqSymm (.eqRefl k)).eqTrans (by unfold index; ipra_ring)))
  exact (pred_succ _).eqSymm.eqTrans ((congrPred eq).eqTrans (pred_succ _))
theorem index_congr (R : PTm n) {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) : Γ ⊢[PRAAx] index R s ≐ index R t := by
  ipra_congr (index (var 0) (var 1) : PTm 2) with [.eqRefl R, h]
theorem index_later (R s t : PTm n) (h : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx] index R t ≐ index R s+monus t s :=
  (index_congr R (eq_add_of_le h)).eqTrans (index_add R s (monus t s))
theorem index_monotone (R s t : PTm n) (h : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx] le (index R s) (index R t) :=
  le_congr (.eqRefl _) (index_later R s t h).eqSymm (le_add_right _ _)
theorem precision_monotone (R s t : PTm n) (h : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx] le (inputPrecision R s) (inputPrecision R t) :=
  add_le_add₂ (add_le_add_right (num 4) h) (le_mul_mono (le_refl (R+two)) (index_monotone R s t h))

theorem precision_unit (R p : PTm n) : Γ ⊢[PRAAx] unit (inputPrecision R p) ≐
    (unit p*pw two (num 4))*pw two ((R+two)*index R p) :=
  (pw_add two (p+num 4) ((R+two)*index R p)).eqTrans
    (congrMul (pw_add two p (num 4)) (.eqRefl _))
theorem precision_budget (R p : PTm n) : Γ ⊢[PRAAx] le
    (num 4*factor R (index R p)*unit p) (unit (inputPrecision R p)) :=
  le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx]
    pw two (num 4)*pw two ((R+two)*index R p)*unit p ≐ (unit p*pw two (num 4))*pw two ((R+two)*index R p)).eqTrans
      (precision_unit R p).eqSymm)
    (le_mul_mono (le_mul_mono (GaussianUnitDiskExponentialName.scale_four (Γ := Γ)) (factor_binary_bound R (index R p))) (le_refl (unit p)))

/-- Real input regularity at the two actual numerical query precisions. -/
theorem query_distance (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (query f R t x) (query f R s x) two (unit (inputPrecision R s)) := by
  let U := unit (inputPrecision R s)
  let V := unit (inputPrecision R t)
  have us := unit_positive (Γ := Γ) (inputPrecision R s)
  have ut := unit_positive (Γ := Γ) (inputPrecision R t)
  have order : Γ ⊢[PRAAx] le U V := GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (precision_monotone R s t hst)
  have budget : Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (add_le_add₂ (le_refl V) order) (le_refl U))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ut us) us budget
    (GaussianNameEquivalence.point_at f x (inputPrecision R t) (inputPrecision R s) h.andE₁)

/-- Compare at the EARLIER cutoff, so its finite Lipschitz constant is
covered by the actual earlier input precision. -/
theorem earlier_cutoff_distance (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum (query f R t x) (index R s)) (value f R s x) one (commonDenominator s) := by
  have raw := GaussianRationalRadiusExponentialLipschitz.scalar_sum_lipschitz _ _ R _ _ (index R s)
    (unit_positive _) (query_bound f R x t h) (query_bound f R x s h) (query_distance f R x s t h hst)
  have budget : Γ ⊢[PRAAx] le ((factor R (index R s)*two)*commonDenominator s) (one*unit (inputPrecision R s)) :=
    le_congr (by
      have e := natEq (pw_succ (Γ := Γ) two s)
      apply deriveNat; unfold commonDenominator unit; ipra_simps; rw [e]; ring)
      (by ipra_ring) (precision_budget R s)
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive _) budget raw

/-- The actual later sum differs from its earlier-cutoff truncation by
the EXISTING scalar factorial-tail certificate, not an assumed output law. -/
theorem cutoff_distance (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (value f R t x) (scalarSum (query f R t x) (index R s)) one (commonDenominator s) := by
  have raw := GaussianRationalExponentialTail.scalar_cutoff_distance (query f R t x) R (s+num 4) (monus t s) (query_bound f R x t h)
  have changed := distance_congr
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc (index_later R s t hst)).eqSymm (.eqRefl _))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) raw
  have grow : Γ ⊢[PRAAx] le (commonDenominator s) (precisionDenominator (s+num 4)) :=
    GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (le_of_eq_add (d := num 6) (by ipra_ring))
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalExponentialTail.precision_positive _) (unit_positive _)
    (le_congr (by ipra_ring) (by ipra_ring) grow) changed

theorem later_comparison (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (value f R t x) (value f R s x) one (unit s) := by
  have combined := distance_triangle_same _ _ _ _ _ _ (unit_positive (succ s))
    (cutoff_distance f R x s t h hst) (earlier_cutoff_distance f R x s t h hst)
  have budget : Γ ⊢[PRAAx] le ((one+one)*unit s) (one*commonDenominator s) := by
    refine le_of_eq_add (d := zero) ?_
    have e := natEq (pw_succ (Γ := Γ) two s)
    apply deriveNat; unfold commonDenominator unit; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive (succ s)) (unit_positive s) budget combined

theorem value_regularity (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    distanceBounded (value f R s x) (value f R t x) (unit s+unit t) (unit s*unit t) := by
  have us := unit_positive (Γ := Γ) s
  have ut := unit_positive (Γ := Γ) t
  refine .orE (lt_or_le s t) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ us.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := unit s*unit s) (by ipra_ring))
      (distance_symmetric _ _ _ _ us.wk (later_comparison f R x s t h.wk (le_of_lt Prf.hyp0)))
  · exact distance_radius_mono _ _ _ _ _ _ ut.wk (positive_product _ _ us.wk ut.wk)
      (le_of_eq_add (d := unit t*unit t) (by ipra_ring)) (later_comparison f R x t s h.wk Prf.hyp0)

/-! Actual output PR2. The bound R is numerical persistent data, not a
fixed external size; f is the fixed original input PR2 schema. -/
def data (R x : PTm n) : PTm n := pairT R x
def nameTerm (f : PR 2) (p y : PTm n) : PTm n := value f (fstT y) p (sndT y)
def nameF (f : PR 2) : PR 2 := PTm.toPR (nameTerm f (var 0) (var 1))
def sample (f : PR 2) (R p x : PTm n) : PTm n := ap2 (nameF f) p (data R x)
ipra_subst data
ipra_subst nameTerm
ipra_subst sample

theorem sample_at (f : PR 2) (R p x : PTm n) : Γ ⊢[PRAAx] sample f R p x ≐ value f R p x := by
  have prog : Γ ⊢[PRAAx] sample f R p x ≐ nameTerm f p (data R x) := by
    simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ) (nameTerm f (var 0) (var 1) : PTm 2) ![p,data R x]
  refine prog.eqTrans ?_
  ipra_congr (value f (var 0) (var 1) (var 2) : PTm 3) with
    [(show _ ⊢[PRAAx] fstT (data R x) ≐ R from fst_pair _ _), .eqRefl p,
      (show _ ⊢[PRAAx] sndT (data R x) ≐ x from snd_pair _ _)] using [nameTerm]
theorem sample_canonical (f : PR 2) (R p x : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample f R p x) :=
  GaussianRationalHorner.canonical_congr (sample_at f R p x) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem sample_regularity (f : PR 2) (R x s t : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    distanceBounded (sample f R s x) (sample f R t x) (unit s+unit t) (unit s*unit t) :=
  distance_congr (sample_at f R s x).eqSymm (sample_at f R t x).eqSymm (.eqRefl _) (.eqRefl _) (value_regularity f R x s t h)
theorem name_regular (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data R x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,sample,Syn.shift,subst_data] using
    sample_regularity f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

/-- Equivalent original inputs at the SAME actual scheduled precision
produce equivalent outputs; no completed exponential properness is assumed. -/
theorem query_equivalence (f g : PR 2) (R x y p : PTm n)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (query f R p x) (query g R p y) two (unit (inputPrecision R p)) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianNameEquivalence.cross_at f g x y (inputPrecision R p) (inputPrecision R p) he)
theorem value_equivalence (f g : PR 2) (R x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (value f R p x) (value g R p y) two (unit p) := by
  have raw := GaussianRationalRadiusExponentialLipschitz.scalar_sum_lipschitz _ _ R _ _ (index R p)
    (unit_positive _) (query_bound f R x p hf) (query_bound g R y p hg) (query_equivalence f g R x y p he)
  have small : Γ ⊢[PRAAx] le ((factor R (index R p)*two)*unit p) (num 4*factor R (index R p)*unit p) :=
    le_of_eq_add (d := two*factor R (index R p)*unit p) (by ipra_ring)
  have larger : Γ ⊢[PRAAx] le (unit (inputPrecision R p)) (two*unit (inputPrecision R p)) :=
    le_of_eq_add (d := unit (inputPrecision R p)) (by ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
    (le_trans small (le_trans (precision_budget R p) larger)) raw

theorem diagonal_proper (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.diagonalEquivalent (nameF f) (nameF g) (data R x) (data R y) := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] input g (Syn.shift R) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hg.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  have result := distance_congr (sample_at f (Syn.shift R) (var 0) (Syn.shift x)).eqSymm
    (sample_at g (Syn.shift R) (var 0) (Syn.shift y)).eqSymm (.eqRefl _) (.eqRefl _)
    (value_equivalence f g (Syn.shift R) (Syn.shift x) (Syn.shift y) (var 0) fs gs es)
  simpa only [GaussianNameEquivalence.diagonalEquivalent,sample,unit,Syn.shift,subst_data] using result
theorem cross_proper (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (he : Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent f g x y) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent (nameF f) (nameF g) (data R x) (data R y) :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (name_regular f R x hf) (name_regular g R y hg)
    (diagonal_proper f g R x y hf hg he)

theorem actual_radius_exponential_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample f (var 0) (var 1) (var 2) ≐
      scalarSum (ap2 f (inputPrecision (var 0) (var 1)) (var 2)) (index (var 0) (var 1))) :=
  closeUniv 3 (sample_at f _ _ _)
theorem actual_radius_exponential_canonical_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalHorner.canonical (sample f (var 0) (var 1) (var 2))) := closeUniv 3 (sample_canonical f _ _ _)
theorem actual_radius_exponential_precision_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (num 4*factor (var 0) (index (var 0) (var 1))*unit (var 1)) (unit (inputPrecision (var 0) (var 1)))) :=
  closeUniv 2 (precision_budget _ _)
theorem actual_radius_exponential_monotone_clock_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ le (inputPrecision (var 0) (var 1)) (inputPrecision (var 0) (var 2))) :=
  closeUniv 3 (.impI (precision_monotone _ _ _ Prf.hyp0))
theorem original_radius_exponential_earlier_cutoff_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 0) (var 1) ⟶ le (var 2) (var 3) ⟶
      distanceBounded (scalarSum (query f (var 0) (var 3) (var 1)) (index (var 0) (var 2)))
        (value f (var 0) (var 2) (var 1)) one (commonDenominator (var 2))) :=
  closeUniv 4 (.impI (.impI (earlier_cutoff_distance f _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_radius_exponential_regularity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 0) (var 1) ⟶
      distanceBounded (sample f (var 0) (var 2) (var 1)) (sample f (var 0) (var 3) (var 1))
        (unit (var 2)+unit (var 3)) (unit (var 2)*unit (var 3))) :=
  closeUniv 4 (.impI (sample_regularity f _ _ _ _ Prf.hyp0))
theorem original_radius_regular_exponential_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))
theorem original_radius_exponential_diagonal_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) ⟶ input g (var 0) (var 2) ⟶ GaussianNameEquivalence.crossEquivalent f g (var 1) (var 2) ⟶
      GaussianNameEquivalence.diagonalEquivalent (nameF f) (nameF g) (data (var 0) (var 1)) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (diagonal_proper f g _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_radius_exponential_cross_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) ⟶ input g (var 0) (var 2) ⟶ GaussianNameEquivalence.crossEquivalent f g (var 1) (var 2) ⟶
      GaussianNameEquivalence.crossEquivalent (nameF f) (nameF g) (data (var 0) (var 1)) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (cross_proper f g _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRadiusExponentialName
