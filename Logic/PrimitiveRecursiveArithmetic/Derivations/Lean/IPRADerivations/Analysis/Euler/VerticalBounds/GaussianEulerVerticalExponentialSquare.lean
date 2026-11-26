import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalProjection
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRealPart
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName

/-!
# Actual exponential squared norms depend only on the real exponent

Keep the same numerical disk on the original exponent and its actual
real-axis projection. The two actual exponential squared-norm names are
equivalent. In particular this binds the unchanged original Euler
integrand to the exponential of its actual real exponent, retaining all
operation and squared-norm observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalExponentialSquare

open_ipra
open GaussianGammaRealValues (projection axisF axis_sample_at axis_regular)
open GaussianExponentialRealPart (doubleRealF doubleRealData squareF squareData squarePrecision double_real_sample double_real_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRadiusExponentialName (input boundedSamples bounded_samples_at)
open GaussianRationalNaturalScale (natScale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem projection_idempotent (q : PTm n) : Γ ⊢[PRAAx] projection (projection q) ≐ projection q :=
  (RationalGaussianRealPart.embed_congr (fst_pair _ _)).eqTrans (RationalGaussianEmbedding.embed_recode _)

theorem double_real_projection_sample (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (doubleRealF f) p (doubleRealData x) ≐ ap2 (doubleRealF (axisF f)) p (doubleRealData x) := by
  let k := GaussianFastValueCut.exponent two p
  have projected : Γ ⊢[PRAAx] projection (ap2 (axisF f) k x) ≐ projection (ap2 f k x) :=
    (RationalGaussianRealPart.embed_congr (congrFst (axis_sample_at f k x))).eqTrans (projection_idempotent _)
  have right := (double_real_sample (Γ := Γ) (axisF f) p x).eqTrans
    (GaussianRationalNaturalScale.natScale_congr (.eqRefl two) projected)
  exact (double_real_sample f p x).eqTrans right.eqSymm

theorem double_real_projection (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    crossEquivalent (doubleRealF f) (doubleRealF (axisF f)) (doubleRealData x) (doubleRealData x) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (double_real_regular f x h) (double_real_regular (axisF f) x (axis_regular f x h))
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianExponentialRealPart.subst_doubleRealData,Syn.shift] using
    double_real_projection_sample f (var 0) (Syn.shift x)

theorem projected_input (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    input (axisF f) R x := by
  refine .andI (axis_regular f x h.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  have raw := GaussianEulerVerticalProjection.projection_bound _ _ _ (le_refl one)
    (bounded_samples_at f (Syn.shift R) (Syn.shift x) (var 0) hs.andE₂)
  have projected := GaussianRationalReciprocal.bound_congr (axis_sample_at f (var 0) (Syn.shift x)).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  simpa only [boundedSamples,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using projected

theorem actual_exponential_square_projection (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    crossEquivalent (squareF (GaussianRadiusExponentialName.nameF f))
      (squareF (GaussianRadiusExponentialName.nameF (axisF f)))
      (squareData (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.data R x))
      (squareData (GaussianRadiusExponentialName.nameF (axisF f)) (GaussianRadiusExponentialName.data R x)) := by
  have projected := projected_input f R x h
  have left := GaussianExponentialRealPart.exponential_norm_square f R x h
  have right := GaussianExponentialRealPart.exponential_norm_square (axisF f) R x projected
  have equal := GaussianExponentialRadiusIndependence.independent_radii_proper (doubleRealF f) (doubleRealF (axisF f))
    (R+R) (R+R) (doubleRealData x) (doubleRealData x)
    (GaussianExponentialRealPart.double_real_input f R x h)
    (GaussianExponentialRealPart.double_real_input (axisF f) R x projected) (double_real_projection f x h.andE₁)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ equal (cross_symm _ _ _ _ right))

theorem original_Euler_vertical_square (z B a b : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b) : Γ ⊢[PRAAx]
    crossEquivalent (squareF GaussianEulerIntegrandName.nameF)
      (squareF (GaussianRadiusExponentialName.nameF (axisF GaussianEulerIntegrandName.exponentF)))
      (squareData GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data z B a b))
      (squareData (GaussianRadiusExponentialName.nameF (axisF GaussianEulerIntegrandName.exponentF))
        (GaussianRadiusExponentialName.data (GaussianEulerIntegrandName.radius z B a b) (GaussianEulerIntegrandName.exponentData z B a b))) :=
  actual_exponential_square_projection GaussianEulerIntegrandName.exponentF _ _ (GaussianEulerIntegrandName.exponent_input z B a b h)

theorem original_Euler_squared_norm_readback (p z B a b : PTm n) : Γ ⊢[PRAAx]
    ap2 (squareF GaussianEulerIntegrandName.nameF) p
      (squareData GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data z B a b)) ≐
      RationalGaussianEmbedding.embed (GaussianRationalMetric.qnormSq
        (ap2 GaussianEulerIntegrandName.nameF
          (squarePrecision GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data z B a b)) (GaussianEulerIntegrandName.data z B a b))) :=
  GaussianExponentialRealPart.square_sample _ _ _

theorem actual_vertical_exponential_squared_norm_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶
      crossEquivalent (squareF (GaussianRadiusExponentialName.nameF f))
        (squareF (GaussianRadiusExponentialName.nameF (axisF f)))
        (squareData (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.data (var 0) (var 1)))
        (squareData (GaussianRadiusExponentialName.nameF (axisF f)) (GaussianRadiusExponentialName.data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (actual_exponential_square_projection f _ _ Prf.hyp0))
theorem original_Euler_vertical_squared_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianEulerIntegrandName.source (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (squareF GaussianEulerIntegrandName.nameF)
        (squareF (GaussianRadiusExponentialName.nameF (axisF GaussianEulerIntegrandName.exponentF)))
        (squareData GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data (var 0) (var 1) (var 2) (var 3)))
        (squareData (GaussianRadiusExponentialName.nameF (axisF GaussianEulerIntegrandName.exponentF))
          (GaussianRadiusExponentialName.data (GaussianEulerIntegrandName.radius (var 0) (var 1) (var 2) (var 3))
            (GaussianEulerIntegrandName.exponentData (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (original_Euler_vertical_square _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalExponentialSquare
