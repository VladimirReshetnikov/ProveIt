import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteQuadraticExpansion

/-!
# The original reciprocal-Gamma sampler has the cubic quadratic expansion

Actual cofinal polynomial observations retain their original coefficient
precision and both computed cutoffs. Original C7 properness and one
finite gap remove only the auxiliary cofinal observation. The requested
P observation and Euler-constant observation remain independent, and the
latter retains its quadratic input factor.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaQuadraticSampler

open_ipra
open GaussianGammaFiniteQuadraticExpansion (quadratic)
open GaussianGammaUnitCoefficientMass (budget)
open GaussianGammaCofinalCoefficientName (coefficientPrecision degreeCutoff exponentialCutoff)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_at_earlier_precisions)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B a b : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (le one b ⋏ (le a b ⋏ bounded (ofGaussian z B) a b))
def numerator (p r R a b : PTm n) : PTm n :=
  budget R*pw a (num 3)*unit p*unit r+pw a two*b*unit p+pw b (num 3)*unit r
def denominator (p r b : PTm n) : PTm n := pw b (num 3)*unit p*unit r

ipra_subst source
ipra_subst numerator
ipra_subst denominator

theorem denominator_positive (p r b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le one (denominator p r b) :=
  positive_product _ _ (positive_product _ _ (GaussianFactorBudget.power_positive b (num 3) hb) (unit_positive p)) (unit_positive r)

/-- A true observation of the original cofinal program, with the actual
coefficient query only coarsened using its proved lower clock. -/
theorem cofinal_expansion (s r z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaCofinalCoefficientName.sample (succ s) z R B) (quadratic r (ofGaussian z B))
      (GaussianGammaFiniteQuadraticExpansion.numerator s r R a b) (GaussianGammaFiniteQuadraticExpansion.denominator s r b) := by
  let q := coefficientPrecision (succ s) R
  let L := degreeCutoff (succ s) R
  let K := exponentialCutoff (succ s) R
  have hk : Γ ⊢[PRAAx] le one K := le_trans (zero_lt_succ s) (GaussianGammaCofinalCoefficientName.exponential_cutoff_cofinal (succ s) R)
  have raw := GaussianGammaFiniteQuadraticExpansion.original_independent_coefficient_error q r R L K (ofGaussian z B) a b
    h.andE₁.andE₁ hk h.andE₂.andE₁ h.andE₂.andE₂.andE₁ (GaussianRationalHorner.ofGaussian_canonical _ _ h.andE₁.andE₂.andE₁) h.andE₂.andE₂.andE₂
  have later : Γ ⊢[PRAAx] le s q := le_trans (le_succ_self s) (GaussianGammaCofinalCoefficientName.coefficient_precision_cofinal (succ s) R)
  have grow := GaussianExponentialReference.unit_monotone later
  have coarse := distance_radius_mono _ _ _ _ (GaussianGammaFiniteQuadraticExpansion.numerator s r R a b)
    (GaussianGammaFiniteQuadraticExpansion.denominator s r b)
    (denominator_positive q r b h.andE₂.andE₁) (denominator_positive s r b h.andE₂.andE₁) (by
      unfold GaussianGammaFiniteQuadraticExpansion.numerator GaussianGammaFiniteQuadraticExpansion.denominator denominator
      ipra_le (𝔞(pw a two)*𝔞 b*𝔞(pw b (num 3))*𝔞(unit r)^2)*sl grow) raw
  exact distance_congr (GaussianGammaCofinalCoefficientName.actual_polynomial_observation (succ s) z R B h.andE₁.andE₂.andE₁)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

private theorem original_cofinal_distance (p s z R B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (GaussianGammaCofinalCoefficientName.sample (succ s) z R B)
      (unit p+unit s) (unit p*unit s) := by
  have raw := GaussianNameEquivalence.cross_at _ _ _ _ p (succ s)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianGammaCofinalCoefficientName.original_C7_identity z R B h))
  exact distance_at_earlier_precisions p s p (succ s) (le_refl p) (le_succ_self s) raw

theorem original_auxiliary_error (p r s z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (GaussianGammaC7Name.sample p z R B) (quadratic r (ofGaussian z B)))
      (numerator p r R a b) (denominator p r b) two s := by
  let D := denominator p r b*unit s
  have hp := unit_positive (Γ := Γ) p
  have hr := unit_positive (Γ := Γ) r
  have hs := unit_positive (Γ := Γ) s
  have hb := h.andE₂.andE₁
  have hd := denominator_positive p r b hb
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hd hs
  have finite := distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] GaussianGammaFiniteQuadraticExpansion.denominator s r b ≐ (pw b (num 3)*unit r)*unit s by
      unfold GaussianGammaFiniteQuadraticExpansion.denominator; ipra_ring) (cofinal_expansion s r z R B a b h)
  have joined := GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ _ _ _ _
    hp (positive_product _ _ (GaussianFactorBudget.power_positive b (num 3) hb) hr) hs
    (original_cofinal_distance p s z R B h.andE₁) finite
  have cube : Γ ⊢[PRAAx] pw b (num 3) ≐ pw b two*b := by
    simpa only [show (num 3 : PTm n) = succ two from rfl] using pw_succ (Γ := Γ) b two
  have small : Γ ⊢[PRAAx] le (pw a two*b) (pw b (num 3)) :=
    le_congr (.eqRefl _) cube.eqSymm (mul_le_mul_right b (pw_le_pw two h.andE₂.andE₂.andE₁))
  have coarsened : Γ ⊢[PRAAx] distanceBounded (GaussianGammaC7Name.sample p z R B) (quadratic r (ofGaussian z B))
      (numerator p r R a b*unit s+two*denominator p r b) D :=
    distance_radius_mono _ _ _ _ _ _ hD hD (by
      dsimp only [D,numerator,denominator,GaussianGammaFiniteQuadraticExpansion.numerator]
      ipra_le (𝔞(pw b (num 3))*𝔞(unit p)^2*𝔞(unit r)^2*𝔞(unit s))*sl small)
      (distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (by dsimp only [D,denominator]; ipra_ring) joined)
  simpa only [GaussianRationalSlackRemoval.slack,GaussianRationalMetric.distanceBounded,unit,D] using coarsened

def gapQuery (p r z R B a b : PTm n) : PTm n := GaussianRationalSlackRemoval.precision
  (qsub (GaussianGammaC7Name.sample p z R B) (quadratic r (ofGaussian z B))) (numerator p r R a b) (denominator p r b) two

theorem original_observations (p r z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (quadratic r (ofGaussian z B))
      (numerator p r R a b) (denominator p r b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two (denominator_positive p r b h.andE₂.andE₁)
    (original_auxiliary_error p r (gapQuery p r z R B a b) z R B a b h)

theorem actual_original_P_cubic_quadratic_sampler_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      distanceBounded (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4))
        (quadratic (var 1) (ofGaussian (var 2) (var 4)))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 6))) :=
  closeUniv 7 (.impI (original_observations _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaQuadraticSampler
