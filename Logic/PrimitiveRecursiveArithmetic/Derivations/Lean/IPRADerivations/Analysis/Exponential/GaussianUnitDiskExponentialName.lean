import IPRADerivations.Analysis.Exponential.Estimates.GaussianRationalExponentialLipschitz
import IPRADerivations.Analysis.Exponential.GaussianRationalExponentialName
import IPRADerivations.Analysis.Names.GaussianNameEquivalence

/-!
# Actual exponentiation of regular names with unit-disk observations

The fixed PR2 input program is observed at p+4. Its actual finite
scalar exponential is cut off by the original exponential-tail clock.
A common numerical cutoff, the checked scalar tail and uniform finite
Lipschitz theorem prove pointCN. Equivalent input names yield equivalent
outputs. Only original pointCN and original sample disks are assumed;
the named logarithm supplier and any general exponential laws are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianUnitDiskExponentialName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalExponentialTail (lastIndex precisionDenominator)
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shifted (p : PTm n) : PTm n := p+num 4
def index (p : PTm n) : PTm n := lastIndex one (shifted p)
def query (f : PR 2) (p x : PTm n) : PTm n := ap2 f (shifted p) x
def value (f : PR 2) (p x : PTm n) : PTm n := scalarSum (query f p x) (index p)
def nameF (f : PR 2) : PR 2 := PTm.toPR (value f (var 0) (var 1))
def sample (f : PR 2) (p x : PTm n) : PTm n := ap2 (nameF f) p x
def unitSamples (f : PR 2) (x : PTm n) : Fm PTm n := .all (bounded (ap2 f (var 0) (Syn.shift x)) one one)
def input (f : PR 2) (x : PTm n) : Fm PTm n := pointCN f x ⋏ unitSamples f x
def scale : PTm n := pw two (num 4)
def commonDenominator (s t : PTm n) : PTm n := scale*unit s*unit t
@[simp] theorem subst_shifted {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (shifted p) = shifted (Syn.subst σ p) := by simp [shifted]
@[simp] theorem subst_index {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (index p) = index (Syn.subst σ p) := by simp [index]
@[simp] theorem subst_query {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (query f p x) = query f (Syn.subst σ p) (Syn.subst σ x) := by simp [query]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (value f p x) = value f (Syn.subst σ p) (Syn.subst σ x) := by simp [value]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (p x : PTm n) :
    Syn.subst σ (sample f p x) = sample f (Syn.subst σ p) (Syn.subst σ x) := by simp [sample]
@[simp] theorem subst_unitSamples {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    (unitSamples f x).subst σ = unitSamples f (Syn.subst σ x) := by simp [unitSamples,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (x : PTm n) :
    (input f x).subst σ = input f (Syn.subst σ x) := by simp [input]
@[simp] theorem subst_scale {l : ℕ} (σ : Fin n → PTm l) : Syn.subst σ (scale : PTm n) = (scale : PTm l) := by simp [scale]
@[simp] theorem subst_commonDenominator {l : ℕ} (σ : Fin n → PTm l) (s t : PTm n) :
    Syn.subst σ (commonDenominator s t) = commonDenominator (Syn.subst σ s) (Syn.subst σ t) := by simp [commonDenominator]

theorem sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] sample f p x ≐ value f p x := by
  simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ) (value f (var 0) (var 1) : PTm 2) ![p,x]
theorem sample_canonical (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample f p x) :=
  GaussianRationalHorner.canonical_congr (sample_at f p x) (GaussianRationalFiniteSum.sum_canonical _ _ _)
theorem unit_samples_at (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] unitSamples f x) : Γ ⊢[PRAAx] bounded (ap2 f p x) one one := by
  simpa [unitSamples] using h.allE p
theorem query_bound (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx] bounded (query f p x) one one :=
  unit_samples_at f x (shifted p) (.andE₂ h)
theorem shifted_unit (p : PTm n) : Γ ⊢[PRAAx] unit (shifted p) ≐ unit p*scale := pw_add two p (num 4)
theorem scale_positive : Γ ⊢[PRAAx] le one (scale : PTm n) := GaussianFactorBudget.power_positive _ _ (le_succ_self one)
theorem scale_four : Γ ⊢[PRAAx] le (num 4) (scale : PTm n) :=
  le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow (num 4))
theorem common_positive (s t : PTm n) : Γ ⊢[PRAAx] le one (commonDenominator s t) :=
  GaussianRationalHorner.positive_product _ _
    (GaussianRationalHorner.positive_product _ _ scale_positive (unit_positive s)) (unit_positive t)

theorem query_distance (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx]
    distanceBounded (query f s x) (query f t x) (unit s+unit t) (commonDenominator s t) := by
  have budget : Γ ⊢[PRAAx] le
      ((unit (shifted s)+unit (shifted t))*commonDenominator s t)
      ((unit s+unit t)*(unit (shifted s)*unit (shifted t))) := by
    have es := natEq (shifted_unit (Γ := Γ) s)
    have et := natEq (shifted_unit (Γ := Γ) t)
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; unfold commonDenominator; ipra_simps; rw [es,et]; ring
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _)) (common_positive s t) budget
    (GaussianNameEquivalence.point_at f x (shifted s) (shifted t) (.andE₁ h))

/-- Genuine cutoff comparison at the SAME original earlier query, with
the numerical common cutoff index(s)+index(t). -/
theorem cutoff_distance (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx]
    distanceBounded (scalarSum (query f s x) (index s+index t)) (value f s x) (unit t) (commonDenominator s t) := by
  have grow : Γ ⊢[PRAAx] le (unit s*scale) (precisionDenominator (shifted s)) :=
    le_congr (shifted_unit s) (.eqRefl _)
      (GaussianFactorBudget.power_monotone_length two (shifted s) (shifted s+num 3) (le_succ_self one) (le_add_right _ _))
  have budget : Γ ⊢[PRAAx] le (one*commonDenominator s t) (unit t*precisionDenominator (shifted s)) :=
    le_congr (by unfold commonDenominator; ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (unit t)) grow)
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalExponentialTail.precision_positive _) (common_positive s t) budget
    (GaussianRationalExponentialTail.scalar_cutoff_distance _ one (shifted s) (index t) (query_bound f x s h))

theorem value_regularity (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx]
    distanceBounded (value f s x) (value f t x) (unit s+unit t) (unit s*unit t) := by
  have middle := GaussianRationalExponentialLipschitz.scalar_sum_lipschitz _ _ _ _ (index s+index t)
    (common_positive s t) (query_bound f x s h) (query_bound f x t h) (query_distance f x s t h)
  have right : Γ ⊢[PRAAx] distanceBounded (scalarSum (query f t x) (index s+index t)) (value f t x)
      (unit s) (commonDenominator s t) :=
    distance_congr (GaussianRationalFiniteSum.sum_index_congr scalarBody (congrSucc (add_comm _ _)) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) (by unfold commonDenominator; ipra_ring) (cutoff_distance f x t s h)
  have combined := distance_triangle_same _ _ _ _ _ _ (common_positive s t)
    (distance_triangle_same _ _ _ _ _ _ (common_positive s t)
      (distance_symmetric _ _ _ _ (common_positive s t) (cutoff_distance f x s t h)) middle) right
  have radius : Γ ⊢[PRAAx] le
      (((unit t+num 3*(unit s+unit t))+unit s)*(unit s*unit t))
      ((unit s+unit t)*commonDenominator s t) :=
    le_congr (by ipra_ring) (by unfold commonDenominator; ipra_ring)
      (le_mul_mono (le_refl ((unit s+unit t)*(unit s*unit t))) scale_four)
  exact distance_radius_mono _ _ _ _ _ _ (common_positive s t)
    (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t)) radius combined

theorem sample_regularity (f : PR 2) (x s t : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx]
    distanceBounded (sample f s x) (sample f t x) (unit s+unit t) (unit s*unit t) :=
  distance_congr (sample_at f s x).eqSymm (sample_at f t x).eqSymm (.eqRefl _) (.eqRefl _) (value_regularity f x s t h)

theorem name_regular (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] input f x) : Γ ⊢[PRAAx] pointCN (nameF f) x := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,sample,unit,Syn.shift] using
    sample_regularity f (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

/-- At the SAME computed cutoff, genuine finite Lipschitz transports the
original two-precision input equivalence to the output diagonal budget. -/
theorem value_equivalence (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f x) (hg : Γ ⊢[PRAAx] input g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (value f p x) (value g p y) two (unit p) := by
  have u := unit_positive (Γ := Γ) (shifted p)
  have common := GaussianRationalHorner.positive_product _ _ u u
  have raw := GaussianRationalExponentialLipschitz.scalar_sum_lipschitz _ _ _ _ (index p)
    common (query_bound f x p hf) (query_bound g y p hg)
      (GaussianNameEquivalence.cross_at f g x y (shifted p) (shifted p) he)
  have three : Γ ⊢[PRAAx] le (num 3) (scale : PTm n) := le_trans (le_succ_self _) scale_four
  have radius : Γ ⊢[PRAAx] le
      ((num 3*(unit (shifted p)+unit (shifted p)))*unit p) (two*(unit (shifted p)*unit (shifted p))) := by
    have e := natEq (shifted_unit (Γ := Γ) p)
    refine le_congr ?_ ?_ (le_mul_mono (le_refl (two*scale*unit p*unit p)) three)
    all_goals apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ common (unit_positive p) radius raw

theorem sample_equivalence (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f x) (hg : Γ ⊢[PRAAx] input g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (sample f p x) (sample g p y) two (unit p) :=
  distance_congr (sample_at f p x).eqSymm (sample_at g p y).eqSymm (.eqRefl _) (.eqRefl _) (value_equivalence f g x y p hf hg he)

theorem diagonal_proper (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f x) (hg : Γ ⊢[PRAAx] input g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    diagonalEquivalent (nameF f) (nameF g) x y := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] input g (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hg.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent f g (Syn.shift x) (Syn.shift y) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  simpa only [diagonalEquivalent,sample,Syn.shift] using sample_equivalence f g (Syn.shift x) (Syn.shift y) (var 0) fs gs es

theorem cross_proper (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f x) (hg : Γ ⊢[PRAAx] input g y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (nameF g) x y :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (name_regular f x hf) (name_regular g y hg) (diagonal_proper f g x y hf hg he)

theorem proper_from_diagonal (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f x) (hg : Γ ⊢[PRAAx] input g y)
    (he : Γ ⊢[PRAAx] diagonalEquivalent f g x y) : Γ ⊢[PRAAx]
    diagonalEquivalent (nameF f) (nameF g) x y :=
  diagonal_proper f g x y hf hg (GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (.andE₁ hf) (.andE₁ hg) he)

theorem actual_unit_disk_exponential_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sample f (var 0) (var 1) ≐ scalarSum (query f (var 0) (var 1)) (index (var 0))) := closeUniv 2 (sample_at f _ _)
theorem actual_unit_disk_exponential_sample_canonical_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalHorner.canonical (sample f (var 0) (var 1))) := closeUniv 2 (sample_canonical f _ _)
theorem original_unit_disk_exponential_common_cutoff_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) ⟶ distanceBounded (scalarSum (query f (var 1) (var 0)) (index (var 1)+index (var 2)))
      (value f (var 1) (var 0)) (unit (var 2)) (commonDenominator (var 1) (var 2))) :=
  closeUniv 3 (.impI (cutoff_distance f _ _ _ Prf.hyp0))
theorem original_unit_disk_exponential_regularity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) ⟶ distanceBounded (sample f (var 1) (var 0)) (sample f (var 2) (var 0))
      (unit (var 1)+unit (var 2)) (unit (var 1)*unit (var 2))) :=
  closeUniv 3 (.impI (sample_regularity f _ _ _ Prf.hyp0))
theorem original_unit_disk_regular_exponential_name_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (input f (var 0) ⟶ pointCN (nameF f) (var 0)) := closeUniv 1 (.impI (name_regular f _ Prf.hyp0))
theorem original_unit_disk_exponential_diagonal_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) ⟶ input g (var 1) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
      diagonalEquivalent (nameF f) (nameF g) (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (diagonal_proper f g _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_unit_disk_exponential_cross_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) ⟶ input g (var 1) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
      crossEquivalent (nameF f) (nameF g) (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (cross_proper f g _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem original_unit_disk_exponential_proper_from_diagonal_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) ⟶ input g (var 1) ⟶ diagonalEquivalent f g (var 0) (var 1) ⟶
      diagonalEquivalent (nameF f) (nameF g) (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (proper_from_diagonal f g _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianUnitDiskExponentialName
