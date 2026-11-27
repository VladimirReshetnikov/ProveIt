import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.Gamma.Digamma.ElementaryBounds.GaussianGammaDigammaHarmonicCells
import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Signs.GaussianGammaNegativeIntervalProductSign
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaProductPascal
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianBudgets.GaussianRationalRelativeTwoTerm

/-!
# Uniform bounds on the literal C24 pole multiplier

The oriented shift product is a positive rational (C/E). Its
two-pole lower bound gives (Ele RC) whenever the pole separations
allow the radius (R). The original C24 multiplier equals the signed
fraction (E/C) by its checked inverse identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianFactorBudget (power_positive)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalNative (product local_margin)
open GaussianGammaNegativeIntervalProductSign (signUnit signedProduct magnitude lowerPoint fraction_readback product_sign)
open GaussianGammaPoleMultiplier (multiplier actual_pole_multiplier_inverse)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul ofGaussian_represents ofGaussian_canonical positive_product qmul_canonical)
open GaussianRationalMatrixFiniteSums (minusOne)
open GaussianRationalMetric (bounded qnormSq bounded_of_cleared comparison_to_cleared)
open GaussianRationalPowerAlgebra (qmul_commutative unit_bounded unit_power norm_one)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingGammaLogarithm (arg)
open RationalArgmin (rationalLE_congr)
open RationalValueBounds (positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem denominator_positive {a b : PTm n} (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] le one b :=
  le_trans h.andE₁ (le_of_lt h.andE₂)

theorem literal_inverse (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] qmul (product a b N) (multiplier (arg a) b (succ N)) ≐ qone :=
  actual_pole_multiplier_inverse (arg a) b one a b (succ N)
    (denominator_positive h) (le_refl one) (denominator_positive h) (local_margin a b h)

private theorem sign_unit_bound (j : PTm n) : Γ ⊢[PRAAx] bounded (signUnit j) one one :=
  unit_bounded _ (unit_power minusOne j ((GaussianRationalRelativeTwoTerm.norm_negative qone).eqTrans norm_one))

private theorem fraction_bound (E C R : PTm n) (hc : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] le E (R*C)) :
    Γ ⊢[PRAAx] bounded (fraction E C) R one :=
  bounded_of_cleared _ (arg E) _ _ _ hc (le_refl one) (ofGaussian_represents _ _ hc)
    (le_congr (by unfold arg; ipra_ring) (by ipra_ring)
      (le_congr (GaussianGammaGaussReference.scaled_one_norm E).eqSymm (.eqRefl _) (le_mul_mono h h)))

theorem bound_from_margin (a b N R : PTm n) (h : Γ ⊢[PRAAx] guard a b)
    (hR : Γ ⊢[PRAAx] le (b*b) (R*(a*monus b a))) :
    Γ ⊢[PRAAx] bounded (multiplier (arg a) b (succ N)) R one := by
  let j := succ N
  let C := magnitude a b j*a
  let E := pw b j*b
  let L := a*monus b a
  let P := product a b N
  let A := signUnit j
  let W := qmul A (fraction E C)
  have hb := denominator_positive h
  have hB := positive_product b b hb hb
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (power_positive _ _ hb) hb
  have read : Γ ⊢[PRAAx] signedProduct a b N ≐ fraction C E :=
    fraction_readback a b N h.andE₁ h.andE₂
  have signed := (product_sign a b N h.andE₁ h.andE₂).andE₂
  have cleared : Γ ⊢[PRAAx] le (E*L) (C*(b*b)) :=
    comparison_to_cleared _ _ _ _ _ _
      (GaussianGammaDigammaHarmonicCells.point_fraction_represents L (b*b) hB)
      (GaussianGammaDigammaHarmonicCells.point_fraction_represents C E hE)
      (rationalLE_congr (.eqRefl _) (congrFst read) signed)
  have cap : Γ ⊢[PRAAx] le E (R*C) := by
    apply positive_cancel (c := b*b) hB
    have hRL : Γ ⊢[PRAAx] le (b*b) (R*L) := hR
    ipra_le 𝔞(E)*sl hRL+𝔞(R)*sl cleared
  have hC : Γ ⊢[PRAAx] le one C :=
    GaussianDominantScalarOrder.factor_positive_left C R (le_congr (.eqRefl _) (mul_comm _ _) (le_trans hE cap))
  have reciprocal : Γ ⊢[PRAAx] qmul (fraction C E) (fraction E C) ≐ qone :=
    (fraction_product C E E C hE hC).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_comm C E) (.eqRefl _)).eqTrans
        (GaussianRationalExponentialTangent.fraction_one (E*C) (positive_product _ _ hE hC)))
  have invert : Γ ⊢[PRAAx] qmul P W ≐ qone :=
    (qmul_associative P A (fraction E C)).eqSymm.eqTrans
      ((qmul_congr ((qmul_commutative P A).eqTrans read) (.eqRefl _)).eqTrans reciprocal)
  have eq : Γ ⊢[PRAAx] W ≐ multiplier (arg a) b j :=
    GaussianEulerBetaProductPascal.inverse_unique P _ _ (qmul_canonical _ _) (qmul_canonical _ _) invert (literal_inverse a b N h)
  exact bound_congr eq (by ipra_ring) (by ipra_ring)
    (bounded_product A (fraction E C) one one R one (le_refl _) (le_refl _)
      (sign_unit_bound j) (fraction_bound E C R hC cap))

theorem base_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] bounded (multiplier (arg a) b (succ N)) (b*b) one := by
  have ha := h.andE₁
  have hg := GaussianGammaNegativeCriticalCorrection.separation_positive a b h.andE₂
  have prod := positive_product _ _ ha hg
  exact bound_from_margin a b N (b*b) h (by ipra_le 𝔞(b)^2*sl prod)

private theorem neighbor_guard (a b D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] guard (D*a+b) (D*b) := by
  have hb := denominator_positive h
  have d : Γ ⊢[PRAAx] le (succ b) D := by ipra_le sl hD+sl hb
  have dpos := le_trans hb (le_of_lt d)
  have gap := h.andE₂
  unfold lt at gap d
  exact .andI (le_trans (positive_product _ _ dpos h.andE₁) (le_add_right _ _))
    (by unfold lt; ipra_le 𝔞(D)*sl gap+sl d)

theorem neighbor_bound (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] le (two*b) D) :
    Γ ⊢[PRAAx] bounded (multiplier (arg (D*a+b)) (D*b) (succ N)) (two*(b*b)) one := by
  let A := D*a+b
  let B := D*b
  let G := monus B A
  have hn := neighbor_guard a b D h hD
  have hA : Γ ⊢[PRAAx] le D A := by
    unfold A
    ipra_le 𝔞(D)*sl h.andE₁+𝔞(b)
  have hG : Γ ⊢[PRAAx] le D (two*G) := by
    have e := natEq (eq_add_of_le (le_of_lt hn.andE₂))
    have gap := h.andE₂
    unfold lt at gap
    dsimp only [G,B,A]
    ipra_le sl hD+2*𝔞(D)*sl gap with -2*e
  have p := le_mul_mono hA hG
  exact bound_from_margin A B N (two*(b*b)) hn
    (by dsimp only [A,B,G] at *; ipra_le 𝔞(b)^2*sl p)

theorem actual_negative_interval_pole_multiplier_bounds_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (guard (var 0) (var 1) ⟶ le (two*var 1) (var 3) ⟶
        (bounded (multiplier (arg (var 0)) (var 1) (succ (var 2))) (var 1*var 1) one ⋏
          bounded (multiplier (arg (var 3*var 0+var 1)) (var 3*var 1) (succ (var 2))) (two*(var 1*var 1)) one)) :=
  closeUniv 4 (.impI (.impI (.andI (base_bound _ _ _ Prf.hyp1) (neighbor_bound _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalInverseBound
