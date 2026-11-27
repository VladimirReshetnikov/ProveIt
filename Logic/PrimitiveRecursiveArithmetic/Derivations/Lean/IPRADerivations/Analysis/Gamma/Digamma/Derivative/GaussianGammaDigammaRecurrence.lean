import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaDerivativeShift
import IPRADerivations.Analysis.Euler.Integration.Decay.Damping.GaussianEulerDampedTimeRate

/-!
# The recurrence for the original positive rational digamma name

The original Gamma derivative recurrence and the reciprocal Gamma
product give ψ(x+1) = ψ(x) + 1/x. All named operations use their
original independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaRecurrence

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaNative (derivativeData derivative_regular reciprocalData reciprocal_regular gamma_times_digamma)
open GaussianGammaReciprocalInverse (gammaF gamma_product constant_inverse)
open GaussianNameArithmetic (addF addData add_fast add_equivalent multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_commutative multiply_one multiply_one_left right_distributive)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product canonical_unique ofGaussian_canonical ofGaussian_represents)
open GaussianRationalSyntheticDivision (qone qone_canonical)
open GaussianStirlingGammaLogarithm (arg source source_shift gammaData gamma_regular gamma_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "PF" => GaussianGammaC7Name.nameF
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def nameF : PR 2 := addF DF constantF
def data (a b : PTm n) : PTm n := addData (dd a b) (fraction b a)

ipra_subst data

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN nameF (data a b) :=
  add_fast _ _ _ _ (GaussianGammaDigammaNative.name_regular a b hs) (constant_regular _)

private theorem fraction_inverse (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] qmul (fraction a b) (fraction b a) ≐ qone := by
  have h := positive_product a b hs.andE₁ hs.andE₂
  have same : Γ ⊢[PRAAx] fraction (a*b) (b*a) ≐ fraction (a*b) (a*b) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (mul_comm b a)
  exact (GaussianEulerDampedTimeRate.fraction_product a b b a hs.andE₂ hs.andE₁).eqTrans
    (same.eqTrans (canonical_unique _ _ _ (a*b) (ofGaussian_canonical _ _ h) qone_canonical h
      (ofGaussian_represents _ _ h) (GaussianRationalReciprocal.qone_represents_scaled (a*b))))

private theorem scaled_derivative (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF constantF gammaF) DF) GaussianGammaDigammaDerivativeShift.productF
      (multiplyData (multiplyF constantF gammaF) DF (GaussianGammaDigammaDifferenceProduct.lowerInputData a b) (dd a b))
      (GaussianGammaDigammaDerivativeShift.productData a b) := by
  let v := fraction a b
  let x := gammaData a b
  let y := dd a b
  let z := derivativeData a b
  have hv := constant_regular (Γ := Γ) v
  have hx := gamma_regular a b hs
  have hy := GaussianGammaDigammaNative.name_regular a b hs
  have hz := derivative_regular a b hs
  have hxy := multiply_fast _ _ _ _ hx hy
  exact cross_trans _ _ _ _ _ _ (multiply_associative constantF gammaF DF v x y hv hx hy)
    (multiply_cross constantF constantF (multiplyF gammaF DF) IF v v (multiplyData gammaF DF x y) z
      hv hv hxy hz (cross_refl _ _ hv) (gamma_times_digamma a b hs))

private theorem cancel_rational_factor (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF (multiplyF constantF gammaF) constantF) gammaF
      (multiplyData (multiplyF constantF gammaF) constantF (GaussianGammaDigammaDifferenceProduct.lowerInputData a b)
        (fraction b a)) (gammaData a b) := by
  let v := fraction a b
  let c := fraction b a
  let x := gammaData a b
  have hv := constant_regular (Γ := Γ) v
  have hc := constant_regular (Γ := Γ) c
  have hx := gamma_regular a b hs
  have permute := multiply_cross (multiplyF constantF gammaF) (multiplyF gammaF constantF) constantF constantF
    (multiplyData constantF gammaF v x) (multiplyData gammaF constantF x v) c c
    (multiply_fast _ _ _ _ hv hx) (multiply_fast _ _ _ _ hx hv) hc hc
    (multiply_commutative constantF gammaF v x hv hx) (cross_refl _ _ hc)
  have assoc := multiply_associative gammaF constantF constantF x v c hx hv hc
  have collapse := multiply_cross gammaF gammaF (multiplyF constantF constantF) oneF x x
    (multiplyData constantF constantF v c) x hx hx (multiply_fast _ _ _ _ hv hc) (one_fast x)
    (cross_refl _ _ hx) (constant_inverse v c x (fraction_inverse a b hs))
  exact cross_trans _ _ _ _ _ _ permute (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ collapse (multiply_one gammaF x hx)))

private theorem reconstructed_derivative (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF gammaF nameF) GaussianGammaDigammaDerivativeShift.nameF
      (multiplyData gammaF nameF (gammaData (a+b) b) (data a b)) (GaussianGammaDigammaDerivativeShift.data a b) := by
  let c := fraction b a
  let y := dd a b
  let x := gammaData a b
  let z := gammaData (a+b) b
  let w := GaussianGammaDigammaDifferenceProduct.lowerInputData a b
  let M := multiplyF constantF gammaF
  let L := multiplyF M DF
  let R := multiplyF M constantF
  have hS := name_regular a b hs
  have hx := gamma_regular a b hs
  have hz := gamma_regular (a+b) b (source_shift a b hs)
  have hy := GaussianGammaDigammaNative.name_regular a b hs
  have hc := constant_regular (Γ := Γ) c
  have hw : Γ ⊢[PRAAx] pointCN M w := multiply_fast _ _ _ _ (constant_regular _) hx
  have replace := multiply_cross gammaF M nameF nameF z w (data a b) (data a b) hz hw hS hS
    (GaussianStirlingGammaLogShift.gamma_increment a b hs) (cross_refl _ _ hS)
  have expand := GaussianNameRingLaws.distributive M DF constantF w y c hw hy hc
  have join := add_equivalent L GaussianGammaDigammaDerivativeShift.productF R gammaF
    (multiplyData M DF w y) (GaussianGammaDigammaDerivativeShift.productData a b) (multiplyData M constantF w c) x
    (multiply_fast _ _ _ _ hw hy) (GaussianGammaDigammaDerivativeShift.product_regular a b hs)
    (multiply_fast _ _ _ _ hw hc) hx (cross_to_diagonal _ _ _ _ (scaled_derivative a b hs))
    (cross_to_diagonal _ _ _ _ (cancel_rational_factor a b hs))
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ expand join)

private theorem cancel_gamma (f : PR 2) (x a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF PF (multiplyF gammaF f)) f
      (multiplyData PF (multiplyF gammaF f) (reciprocalData a b) (multiplyData gammaF f (gammaData a b) x)) x := by
  let y := reciprocalData a b
  let z := gammaData a b
  let M := multiplyF PF gammaF
  let v := multiplyData PF gammaF y z
  have hy := reciprocal_regular a b hs
  have hz := gamma_regular a b hs
  have inv := cross_trans _ _ _ _ _ _ (gamma_product (arg a) a b one b (gamma_source a b hs))
    (GaussianBoundedInverseApartness.ones_equivalent y x)
  have collapse := multiply_cross M oneF f f v x x x (multiply_fast _ _ _ _ hy hz) (one_fast x)
    hf hf inv (cross_refl _ _ hf)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative PF gammaF f y z x hy hz hf))
    (cross_trans _ _ _ _ _ _ collapse (multiply_one_left f x hf))

set_option maxHeartbeats 1000000 in
theorem digamma_shift (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent DF nameF (dd (a+b) b) (data a b) := by
  let z := gammaData (a+b) b
  let x := dd (a+b) b
  let y := data a b
  let r := reciprocalData (a+b) b
  have hi := source_shift a b hs
  have hz := gamma_regular _ _ hi
  have hx := GaussianGammaDigammaNative.name_regular _ _ hi
  have hy := name_regular a b hs
  have hr := reciprocal_regular _ _ hi
  have times := cross_trans _ _ _ _ _ _ (gamma_times_digamma _ _ hi)
    (cross_trans _ _ _ _ _ _ (GaussianGammaDigammaDerivativeShift.derivative_shift a b hs)
      (cross_symm _ _ _ _ (reconstructed_derivative a b hs)))
  have lift := multiply_cross PF PF (multiplyF gammaF DF) (multiplyF gammaF nameF) r r
    (multiplyData gammaF DF z x) (multiplyData gammaF nameF z y) hr hr
    (multiply_fast _ _ _ _ hz hx) (multiply_fast _ _ _ _ hz hy) (cross_refl _ _ hr) times
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (cancel_gamma DF x (a+b) b hx hi))
    (cross_trans _ _ _ _ _ _ lift (cancel_gamma nameF y (a+b) b hy hi))

theorem actual_original_digamma_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent DF nameF (dd (var 0+var 1) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (digamma_shift _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaRecurrence
