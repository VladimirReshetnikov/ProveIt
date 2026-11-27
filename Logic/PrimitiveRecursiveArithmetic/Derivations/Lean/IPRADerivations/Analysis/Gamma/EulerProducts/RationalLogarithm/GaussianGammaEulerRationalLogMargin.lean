import IPRADerivations.Analysis.Gamma.EulerProducts.RationalLogarithm.GaussianGammaEulerRationalLog
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerInverseConvergence
import IPRADerivations.Analysis.Euler.VerticalBounds.Projections.GaussianEulerVerticalProjection

/-!
# Uniform positive margin for cofinal finite Euler inverses

The original Gamma lower margin (1/18) and the certified inverse Euler
error give a common margin (1/36) for sufficiently late cutoffs.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogMargin

open_ipra
open ComplexLogarithmRemainder (oneCode re)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerVerticalProjection (projected_source)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaRealValues (axisF)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianNamedRightHalfPlane (marginPoint certificate)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (ofGaussian_canonical ofGaussian_represents positive_product)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianStirlingGammaLogarithm (arg gammaData gammaMargin gamma_lower_at)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper upper_of_radius upper_congr upper_mono upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def margin : PTm n := num 36
def cutoff (a b : PTm n) : PTm n :=
  two*a+GaussianGammaPerturbationExponent.numerator a+margin*coefficientNumerator a b
def source (N a b : PTm n) : Fm PTm n := GaussianStirlingGammaLogarithm.source a b ⋏ le (cutoff a b) N
def inverseData (N a b : PTm n) : PTm n := eulerData (arg a) a b b N

ipra_subst cutoff [margin, two]
ipra_subst source
ipra_subst inverseData [arg, eulerData, GaussianGammaEulerReciprocalInverse.eulerHeight]

theorem margin_positive : Γ ⊢[PRAAx] le one (margin : PTm n) := by
  unfold margin
  ipra_le 35

theorem cutoff_source (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source (arg a) a b one b N := by
  have e₁ : Γ ⊢[PRAAx] le (two*a) (cutoff a b) :=
    le_trans (le_add_right _ (GaussianGammaPerturbationExponent.numerator a)) (le_add_right _ _)
  have e₂ : Γ ⊢[PRAAx] le (GaussianGammaPerturbationExponent.numerator a) (cutoff a b) :=
    le_trans (le_add_left _ (two*a)) (le_add_right _ _)
  exact .andI (GaussianStirlingGammaLogarithm.gamma_source a b h.andE₁)
    (.andI (le_trans e₁ h.andE₂) (le_trans e₂ h.andE₂))

theorem cutoff_positive (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) : Γ ⊢[PRAAx] le one N :=
  GaussianGammaEulerInverseConvergence.cutoff_positive _ _ _ _ _ _ (cutoff_source N a b h)

theorem denominator_positive (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] le one (coefficientDenominator a one N) :=
  GaussianGammaEulerInverseConvergence.coefficient_denominator_positive _ _ _ _ _ _ (cutoff_source N a b h)

theorem cutoff_budget (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] le (margin*coefficientNumerator a b) (coefficientDenominator a one N) := by
  let A := GaussianGammaReciprocalInverse.lambdaNumerator a (one : PTm n)
  have ap : Γ ⊢[PRAAx] le one A :=
    (GaussianGammaReciprocalInverse.lambda_positive a one b (le_refl one) h.andE₁.andE₂).andE₁
  have l : Γ ⊢[PRAAx] le (one*N) ((A*A)*N) := mul_le_mul_right N (positive_product _ _ ap ap)
  exact le_trans (le_trans (le_add_left _ _) h.andE₂) (le_congr (one_mul N) (.eqRefl _) l)

theorem margin_scalar (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] fstT (marginPoint A) ≐ GaussianEuclideanDistanceName.fraction one A := by
  apply RationalFiniteSum.canonical_equal _ _ (re oneCode) (ZT.ofNat one) _ _
    (ofGaussian_canonical oneCode _ hA).andE₂.andE₁ (RationalNormalForm.normalize_well_formed _ _ hA)
    (ofGaussian_represents oneCode _ hA).andE₁ (GaussianEuclideanDistanceName.fraction_represents _ _ hA) hA hA
  apply ZT.derive
  simp only [ZT.toZ_mul,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,IPRA.Q.mk_one,map_one]

private theorem lower_from_margin_slack (q E D : PTm n)
    (h : Γ ⊢[PRAAx] upper (GaussianEuclideanDistanceName.fraction one gammaMargin) (fstT q)
      (margin*E+D) (margin*D)) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint (margin : PTm n))) (fstT q) E D := by
  let b := denominatorOf (fstT q)
  let v := numeratorOf (fstT q)
  let a : ZT n := ZT.ofNat one
  let L := RationalRepresentedUpper.left a b (margin*D)
  let R := RationalRepresentedUpper.right v gammaMargin b (margin*E+D) (margin*D)
  have hm : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by unfold gammaMargin; ipra_le 17
  have hM := margin_positive (Γ := Γ) (n := n)
  have old : Γ ⊢[PRAAx] zle L R :=
    RationalRepresentedUpper.to_signed _ _ a v gammaMargin b (margin*E+D) (margin*D)
      (GaussianEuclideanDistanceName.fraction_represents _ _ hm) (RationalRepresentations.represents_self _) h
  refine upper_congr (margin_scalar margin hM).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) ?_
  apply RationalRepresentedUpper.from_signed _ _ a v margin b E D hM (RationalArgmin.denominator_positive (fstT q))
    (GaussianEuclideanDistanceName.fraction_represents _ _ hM) (RationalRepresentations.represents_self _)
  apply PolynomialBisection.zle_scale_cancel (c := gammaMargin) hm
  apply zle_of_toZ (PolynomialBisection.slack L R)
  have e := zle_toZ old
  dsimp only [PolynomialBisection.slack,L,R,a,margin,gammaMargin] at e ⊢
  simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination e

theorem margin_at (t p N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] upper (fstT (marginPoint (margin : PTm n))) (fstT (ap2 eulerF p (inverseData N a b)))
      (unit t+unit p) (unit t*unit p) := by
  let K := coefficientNumerator a b
  let D := coefficientDenominator a one N
  let T := unit t
  let U := unit p
  let V := two*T
  let d := inverseData N a b
  let y := ap2 gammaF (succ t) (gammaData a b)
  let x := ap2 eulerF p d
  have hD := denominator_positive N a b h
  have hU := unit_positive (Γ := Γ) p
  have hT := unit_positive (Γ := Γ) t
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (le_succ_self one) hT
  have unitEq : Γ ⊢[PRAAx] unit (succ t) ≐ V := (pw_succ two t).eqTrans (mul_comm _ _)
  have e0 := GaussianGammaEulerInverseConvergence.actual_observation_error p (succ t) (arg a) a b one b N
    (cutoff_source N a b h)
  have eN : Γ ⊢[PRAAx] rateNumerator K D p (succ t) ≐ K*U*V+D*(U+V) :=
    congrAdd (congrMul (.eqRefl _) unitEq) (congrMul (.eqRefl _) (congrAdd (.eqRefl _) unitEq))
  have eD : Γ ⊢[PRAAx] rateDenominator D p (succ t) ≐ D*U*V := congrMul (.eqRefl _) unitEq
  have hp := positive_product _ _ (positive_product _ _ hD hU) hV
  have dist := GaussianRationalDistanceOrder.distance_congr (.eqRefl x) (.eqRefl y) eN eD e0
  have upper := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hp (distance_symmetric _ _ _ _ hp dist))
  have lo := upper_congr (.eqRefl _) (.eqRefl (fstT y)) (.eqRefl _) unitEq (gamma_lower_at (succ t) a b h.andE₁)
  have joined := upper_triangle _ _ _ _ _ _ _ lo upper
  apply lower_from_margin_slack
  refine upper_mono _ _ _ _ _ _ (positive_product _ _ hV hp) joined ?_
  change Γ ⊢[PRAAx] le ((one*(D*U*V)+(K*U*V+D*(U+V))*V)*(margin*(T*U)))
    ((margin*(T+U)+T*U)*(V*(D*U*V)))
  dsimp only [V]
  ipra_le 4*(𝔞 U)^2*(𝔞 T)^3*sl (cutoff_budget N a b h)

theorem inverse_source (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source eulerF (inverseData N a b) margin := by
  refine .andI (GaussianGammaEulerInverseConvergence.actual_names_regular _ _ _ _ _ _ (cutoff_source N a b h)).andE₁
    (.andI margin_positive (.allI (.allI ?_)))
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh N) (sh a) (sh b) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh,Δ] using h.shift.shift
  have finite := margin_at (var 1) (var 0) (sh N) (sh a) (sh b) hs
  have e := constant_at (Γ := Δ) (var 1) (marginPoint (margin : PTm (n+2)))
  simpa only [certificate,realOrder,GaussianNamedRightHalfPlane.subst_marginPoint,LeanProofs.IPRA.PTm.subst_num,
    margin,subst_inverseData,Syn.shift,sh,Δ] using
      upper_congr (congrFst e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) finite

theorem projected_inverse_source (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source (axisF eulerF) (inverseData N a b) margin :=
  projected_source _ _ _ (inverse_source N a b h)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogMargin
