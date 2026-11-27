import IPRADerivations.Analysis.Exponential.PositiveAxis.FiniteEstimates.GaussianPositiveExponentialOrder
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialReference
import IPRADerivations.Analysis.Gamma.Names.Symmetry.GaussianGammaRealValues

/-!
# Independent observations of ordered positive exponentials

The original separately clocked exponential names are compared through
the same actual finite cutoff at a common input precision. Finite order
and the two original reference errors give exactly the two requested
observation errors. Neither output order nor a common name clock is an
input. The explicit nonnegative input-sample predicates are discharged
for original constant positive rational inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveExponentialOrder

open_ipra
open GaussianPositiveRealArithmetic (positive positive_congr)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianRadiusExponentialName (input inputPrecision index nameF data sample)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open RationalArgmin (rationalLE)
open RationalValueBounds (upper radius upper_of_radius upper_order_right upper_triangle)
open GaussianGammaCanonicalExponent (constantF constant_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveSamples (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (positive (ap2 f (var 0) (Syn.shift x)))
def sampleOrder (f g : PR 2) (x y : PTm n) : Fm PTm n := .all
  (rationalLE (fstT (ap2 f (var 0) (Syn.shift x))) (fstT (ap2 g (var 0) (Syn.shift y))))
def realOrder (f g : PR 2) (x y : PTm n) : Fm PTm n := .all (.all
  (upper (fstT (ap2 f (var 1) (Syn.shift (Syn.shift x))))
    (fstT (ap2 g (var 0) (Syn.shift (Syn.shift y))))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))))

ipra_subst positiveSamples [Syn.subst_shift, Syn.shift_subst]
ipra_subst sampleOrder [Syn.subst_shift, Syn.shift_subst]
ipra_subst realOrder [Syn.subst_shift, Syn.shift_subst]

theorem positive_at (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] positiveSamples f x) :
    Γ ⊢[PRAAx] positive (ap2 f p x) := by simpa [positiveSamples] using h.allE p
theorem order_at (f g : PR 2) (x y p : PTm n) (h : Γ ⊢[PRAAx] sampleOrder f g x y) :
    Γ ⊢[PRAAx] rationalLE (fstT (ap2 f p x)) (fstT (ap2 g p y)) := by simpa [sampleOrder] using h.allE p
theorem real_order_at (f g : PR 2) (x y p q : PTm n) (h : Γ ⊢[PRAAx] realOrder f g x y) : Γ ⊢[PRAAx]
    upper (fstT (ap2 f p x)) (fstT (ap2 g q y)) (unit p+unit q) (unit p*unit q) := by
  have pair : Γ ⊢[PRAAx] .all (upper (fstT (ap2 f (Syn.shift p) (Syn.shift x)))
      (fstT (ap2 g (var 0) (Syn.shift y)))
      (unit (Syn.shift p)+unit (var 0)) (unit (Syn.shift p)*unit (var 0))) := by
    simpa only [realOrder,Fm.subst_all,RationalValueBounds.subst_upper,subst_fstT,subst_ap2,
      PTm.subst_add,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,
      Syn.up_zero,Syn.up_one,Syn.up_succ,Foundations.BoundedFormulas.subst_up_shift',
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using h.allE p
  simpa only [RationalValueBounds.subst_upper,subst_fstT,subst_ap2,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,
    Syn.subst_var,Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift] using pair.allE q

theorem scalar_coordinate_distance (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx] radius (fstT q) (fstT r) A B :=
  GaussianGammaRealValues.scalar_radius_of_embedded_distance _ _ A B hB
    (GaussianGammaRealValues.projection_distance q r A B hB h)

theorem exponential_samples_positive (f : PR 2) (R x p : PTm n)
    (hf : Γ ⊢[PRAAx] positiveSamples f x) : Γ ⊢[PRAAx]
    positive (ap2 (nameF f) p (data R x)) :=
  positive_congr (GaussianRadiusExponentialName.sample_at f R p x).eqSymm
    (GaussianPositiveExponentialProduct.positive_scalar_sum _ _ (positive_at f x (inputPrecision R p) hf))

theorem exponential_positive (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] positiveSamples f x) :
    Γ ⊢[PRAAx] positiveSamples (nameF f) (data R x) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] positiveSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  simpa only [positiveSamples,Syn.shift,GaussianRadiusExponentialName.subst_data] using
    exponential_samples_positive f (Syn.shift R) (Syn.shift x) (var 0) hs

theorem independent_observations (f g : PR 2) (R S x y p q : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (hfp : Γ ⊢[PRAAx] positiveSamples f x) (hgp : Γ ⊢[PRAAx] positiveSamples g y)
    (hOrder : Γ ⊢[PRAAx] sampleOrder f g x y) : Γ ⊢[PRAAx]
    upper (fstT (ap2 (nameF f) p (data R x))) (fstT (ap2 (nameF g) q (data S y)))
      (unit p+unit q) (unit p*unit q) := by
  let j := inputPrecision R p+inputPrecision S q
  let K := index R p+index S q
  let u := scalarSum (ap2 f j x) K
  let v := scalarSum (ap2 g j y) K
  have left := GaussianExponentialReference.finite_reference f R x p j K hf (le_add_right _ _) (le_add_right _ _)
  have right := GaussianExponentialReference.finite_reference g S y q j K hg (le_add_left _ _) (le_add_left _ _)
  have leftRadius : Γ ⊢[PRAAx] radius (fstT (ap2 (nameF f) p (data R x))) (fstT u) one (unit p) :=
    RationalValueBounds.radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ one (unit p) (unit_positive p) left)
  have rightRadius : Γ ⊢[PRAAx] radius (fstT v) (fstT (ap2 (nameF g) q (data S y))) one (unit q) :=
    scalar_coordinate_distance _ _ one (unit q) (unit_positive q) right
  have middle : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v) :=
    GaussianPositiveExponentialOrder.scalar_sum_monotone _ _ K (positive_at f x j hfp) (positive_at g y j hgp)
      (order_at f g x y j hOrder)
  have first := upper_order_right _ _ _ one (unit p) (upper_of_radius _ _ _ _ leftRadius) middle
  exact RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (upper_triangle _ _ _ one (unit p) one (unit q) first (upper_of_radius _ _ _ _ rightRadius))

theorem exponential_order (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (hfp : Γ ⊢[PRAAx] positiveSamples f x) (hgp : Γ ⊢[PRAAx] positiveSamples g y)
    (hOrder : Γ ⊢[PRAAx] sampleOrder f g x y) : Γ ⊢[PRAAx]
    realOrder (nameF f) (nameF g) (data R x) (data S y) := by
  refine .allI (.allI ?_)
  have fs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift.shift
  have gs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input g (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using hg.shift.shift
  have ps : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] positiveSamples f (Syn.shift (Syn.shift x)) :=
    by simpa [Fm.shift,Syn.shift] using hfp.shift.shift
  have qs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] positiveSamples g (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using hgp.shift.shift
  have os : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] sampleOrder f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using hOrder.shift.shift
  simpa only [realOrder,Syn.shift,GaussianRadiusExponentialName.subst_data] using independent_observations f g
    (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
    (var 1) (var 0) fs gs ps qs os

theorem constant_positive (x : PTm n) (h : Γ ⊢[PRAAx] positive x) : Γ ⊢[PRAAx] positiveSamples constantF x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [positiveSamples,Syn.shift] using positive_congr (constant_at (var 0) (Syn.shift x)).eqSymm hs

theorem constant_order (x y : PTm n) (h : Γ ⊢[PRAAx] rationalLE (fstT x) (fstT y)) :
    Γ ⊢[PRAAx] sampleOrder constantF constantF x y := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (fstT (Syn.shift x)) (fstT (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleOrder,Syn.shift] using RationalArgmin.rationalLE_congr
    (congrFst (constant_at (var 0) (Syn.shift x))).eqSymm (congrFst (constant_at (var 0) (Syn.shift y))).eqSymm hs

theorem original_positive_rational_exponential_order (x y : PTm n)
    (hx : Γ ⊢[PRAAx] positive x) (hy : Γ ⊢[PRAAx] positive y)
    (h : Γ ⊢[PRAAx] rationalLE (fstT x) (fstT y)) : Γ ⊢[PRAAx]
    realOrder (nameF constantF) (nameF constantF)
      (GaussianGammaFiniteApproximantName.exponentialInputData constantF x)
      (GaussianGammaFiniteApproximantName.exponentialInputData constantF y) :=
  exponential_order constantF constantF _ _ x y
    (GaussianGammaFiniteApproximantName.exponential_input constantF x (GaussianGammaCanonicalExponent.constant_regular x))
    (GaussianGammaFiniteApproximantName.exponential_input constantF y (GaussianGammaCanonicalExponent.constant_regular y))
    (constant_positive x hx) (constant_positive y hy) (constant_order x y h)

theorem original_positive_exponential_independent_order_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 0) (var 2) ⟶ input g (var 1) (var 3) ⟶ positiveSamples f (var 2) ⟶ positiveSamples g (var 3) ⟶
      sampleOrder f g (var 2) (var 3) ⟶ realOrder (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (exponential_order f g _ _ _ _ (Prf.hyp1.wk.wk.wk : _) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem original_positive_constant_exponential_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positive (var 0) ⟶ positive (var 1) ⟶ rationalLE (fstT (var 0)) (fstT (var 1)) ⟶
      realOrder (nameF constantF) (nameF constantF)
        (GaussianGammaFiniteApproximantName.exponentialInputData constantF (var 0))
        (GaussianGammaFiniteApproximantName.exponentialInputData constantF (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (original_positive_rational_exponential_order _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem actual_positive_exponential_samples_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positiveSamples f (var 1) ⟶ positiveSamples (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_positive f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveExponentialOrder
