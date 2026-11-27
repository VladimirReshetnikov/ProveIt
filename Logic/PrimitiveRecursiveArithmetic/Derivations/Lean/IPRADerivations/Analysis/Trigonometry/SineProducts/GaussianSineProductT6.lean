import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianInverseSquareProductComparison
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductT4Budget
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance

/-!
# Finite sine-product comparison and (T4) error assembly

The inverse-square envelope controls the actual finite products in the
(T6) comparison. The comparison takes pointwise bounds on the
trigonometric rows and does not require a lower bound on the cutoff
beyond positivity. It also accounts for a sinc prefactor within
(8R^2/m^2) of one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT6

open_ipra
open GaussianRationalPowerDifference (bounded_sum_one)
open GaussianSineProductT4Budget (halfIndex squareDenominator headError productError prefactorError rate
  absorb_errors cutoff_le_half_index)
open GaussianInverseSquareProductTail (factorBounds factor_bound_at sharp_tail sine_factor_bound)
open GaussianInverseSquareProductGrowth (uniform_bound)
open GaussianInverseSquareProductComparison (rowErrors compare_products)
open GaussianGammaEulerReflectionHead (body sineProduct square_factor_at)
open GaussianRationalFiniteProduct (qprod product_split product_index_congr product_canonical)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianBalancedRadiusArithmetic (unit_monotone)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (qone bound_congr bounded_sum bounded_negative)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_radius_mono_same)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianReciprocalHorner (qmul_one_right)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def factorSize (R : PTm n) : PTm n := num 16*(R*R)

ipra_subst factorSize

theorem reference_factors (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] factorBounds body (pairT z B) (factorSize R) zero := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let a := Syn.shift z
  let r := Syn.shift R
  let d := Syn.shift B
  let j : PTm (n+1) := Syn.shift (zero : PTm n)+var 0
  have hd : Δ ⊢[PRAAx] le one d := by simpa [Fm.shift,Syn.shift,Δ,d,one] using hB.shift
  have ha : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded a (r*d) := by
    simpa [Fm.shift,Syn.shift,Δ,a,r,d] using hz.shift
  have p : Δ ⊢[PRAAx] le one (succ j*succ j) := positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)
  have mono : Δ ⊢[PRAAx] le (r*r) (factorSize r) := by
    unfold factorSize
    exact le_of_eq_add (d := num 15*(r*r)) (by ipra_ring)
  have step := distance_radius_mono_same p mono (sine_factor_bound j a r d hd ha)
  have result : Δ ⊢[PRAAx] distanceBounded (inst2 body j (pairT a d)) qone (factorSize r) (succ j*succ j) :=
    distance_congr (square_factor_at j a d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) step
  change Δ ⊢[PRAAx] distanceBounded (inst2 body j (Syn.shift (pairT z B))) qone
    (Syn.shift (factorSize R)) (succ j*succ j)
  simpa only [Δ,a,r,d,subst_factorSize,subst_pairT,Syn.shift] using result

private theorem shifted_factors (f : PTm 2) (x C K : PTm n)
    (h : Γ ⊢[PRAAx] factorBounds f x C zero) : Γ ⊢[PRAAx] factorBounds f x C K := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let x' := Syn.shift x
  let C' := Syn.shift C
  let K' := Syn.shift K
  let j : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] factorBounds f x' C' zero := by simpa [Fm.shift,Syn.shift,Δ,x',C'] using h.shift
  have e : Δ ⊢[PRAAx] zero+(K'+j) ≐ K'+j := zero_add _
  exact distance_congr (congrInst2 f e (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (congrMul (congrSucc e) (congrSucc e)) (factor_bound_at f x' C' zero (K'+j) hs)

private theorem growth_budget (R : PTm n) (hR : Γ ⊢[PRAAx] le one R) :
    Γ ⊢[PRAAx] le (two*unit (two*factorSize R)) (unit (num 68*(R*R))) := by
  let H := R*R
  have sq : Γ ⊢[PRAAx] le one H := positive_product R R hR hR
  have exponent : Γ ⊢[PRAAx] le (succ (two*factorSize R)) (num 68*H) := by
    unfold factorSize
    dsimp only [H] at sq ⊢
    ipra_le 35*𝔞 R*𝔞 R+sl sq
  exact le_congr ((pw_succ two (two*factorSize R)).eqTrans (mul_comm _ _)) (.eqRefl _)
    (unit_monotone _ _ exponent)

private theorem growth_le (R : PTm n) :
    Γ ⊢[PRAAx] le (unit (two*factorSize R)) (unit (num 68*(R*R))) :=
  unit_monotone _ _ (by unfold factorSize; ipra_le 36*𝔞 R*𝔞 R)

private theorem tail_large (f : PTm 2) (x R K J : PTm n)
    (hK : Γ ⊢[PRAAx] le one K) (hcut : Γ ⊢[PRAAx] le (two*factorSize R) K)
    (hJ : Γ ⊢[PRAAx] le K J) (hf : Γ ⊢[PRAAx] factorBounds f x (factorSize R) zero) :
    Γ ⊢[PRAAx] distanceBounded (qprod f J x) (qprod f K x)
      (unit (num 68*(R*R))*(num 32*(R*R))) K := by
  let C := factorSize R
  let r := monus J K
  let P := qprod f K x
  let T := GaussianInverseSquareProductTail.product f K r x
  let G := unit (two*C)
  let W := unit (num 68*(R*R))
  have D := GaussianInverseSquareProductTail.denominator_positive K r hK
  have h := sharp_tail f x C K r hK hcut (shifted_factors f x C K hf)
  have eq : Γ ⊢[PRAAx] qprod f J x ≐ qmul P T :=
    (product_index_congr f (eq_add_of_le hJ) (.eqRefl _)).eqTrans (product_split f K r x)
  have raw := distance_congr eq.eqSymm (qmul_one_right P (product_canonical f K x))
    (.eqRefl _) (.eqRefl _) (multiply_distance P T qone G (two*C*r) (K*(K+r)) D (uniform_bound f x C K hf) h)
  have scaled : Γ ⊢[PRAAx] distanceBounded (qprod f J x) P (G*(two*C)) K :=
    distance_radius_mono _ _ _ _ _ _ D hK (by ipra_le 𝔞 G*2*𝔞 C*𝔞 K*𝔞 K) raw
  have mono : Γ ⊢[PRAAx] le G W := growth_le R
  exact distance_radius_mono _ _ _ _ _ _ hK hK
    (le_congr (by ipra_ring) (by dsimp only [W,C,factorSize]; ipra_ring)
      (le_mul_mono mono (le_refl (two*C*K))))
    scaled

theorem tail_estimate (f : PTm 2) (x R K J : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (hJ : Γ ⊢[PRAAx] le K J) (hf : Γ ⊢[PRAAx] factorBounds f x (factorSize R) zero) :
    Γ ⊢[PRAAx] distanceBounded (qprod f J x) (qprod f K x) (unit (num 68*(R*R))*(num 32*(R*R))) K := by
  let G := unit (two*factorSize R)
  let W := unit (num 68*(R*R))
  let C := factorSize R
  refine .orE (le_total (two*C) K) (tail_large f x R K J hK.wk Prf.hyp0 hJ.wk hf.wk) ?_
  have small : le K (two*C) :: Γ ⊢[PRAAx] le K (two*C) := Prf.hyp0
  have hP := uniform_bound (Γ := le K (two*C) :: Γ) f x C J hf.wk
  have hQ := uniform_bound (Γ := le K (two*C) :: Γ) f x C K hf.wk
  have raw : le K (two*C) :: Γ ⊢[PRAAx] distanceBounded (qprod f J x) (qprod f K x) (two*G) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (bounded_sum_one hP (bounded_negative _ _ _ (le_refl one) hQ))
  exact distance_radius_mono _ _ _ _ _ _ (le_refl one) hK.wk
    (le_congr (.eqRefl _) (by unfold C factorSize; ipra_ring)
      (le_mul_mono (growth_budget R hR.wk) small)) raw

theorem t6 (f : PTm 2) (x z R B K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hf : Γ ⊢[PRAAx] factorBounds f x (factorSize R) zero)
    (he : Γ ⊢[PRAAx] rowErrors f body x (pairT z B) (num 96*(R*R)) (R*R) (squareDenominator R K) K) :
    Γ ⊢[PRAAx] distanceBounded (qprod f (halfIndex R K) x) (sineProduct z B K)
      (productError R K (num 32)) (K*squareDenominator R K) := by
  let C := factorSize R
  let H := R*R
  let D := squareDenominator R K
  let G := unit (two*C)
  let W := unit (num 68*H)
  let J := halfIndex R K
  have hD := GaussianSineProductT4Budget.denominator_positive (Γ := Γ) R K
  have den := positive_product K D hK hD
  have tail : Γ ⊢[PRAAx] distanceBounded (qprod f J x) (qprod f K x) (W*(num 32*H)) K :=
    tail_estimate f x R K J hR hK (cutoff_le_half_index R K hR hK) hf
  have head := compare_products f body x (pairT z B) C (num 96*H) H D K hD hf
    (reference_factors z R B hB hz) he
  have hl := distance_radius_mono _ _ _ _ (W*(num 32*H)*D) _ hK den
    (le_of_eq_add (d := zero) (by ipra_ring)) tail
  have mono : Γ ⊢[PRAAx] le G W := growth_le R
  have hr := distance_radius_mono _ _ _ _ (W*headError R K*K) _ hD den
    (le_congr (by unfold headError; dsimp only [G,H]; ipra_ring) (by ipra_ring)
      (le_mul_mono mono (le_refl (headError R K*K*D)))) head
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold productError; dsimp only [W,H,D]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den hl hr)

theorem prefactor_estimate (f : PTm 2) (x s R K : PTm n)
    (hf : Γ ⊢[PRAAx] factorBounds f x (factorSize R) zero)
    (hs : Γ ⊢[PRAAx] distanceBounded s qone (num 8*(R*R)) (squareDenominator R K)) :
    Γ ⊢[PRAAx] distanceBounded (qmul s (qprod f (halfIndex R K) x)) (qprod f (halfIndex R K) x)
      (prefactorError R) (squareDenominator R K) := by
  let P := qprod f (halfIndex R K) x
  let C := factorSize R
  let D := squareDenominator R K
  let G := unit (two*C)
  let W := unit (num 64*(R*R))
  have hD := GaussianSineProductT4Budget.denominator_positive (Γ := Γ) R K
  have raw := distance_congr (qmul_commutative P s) (qmul_one_right P (product_canonical f _ x))
    (.eqRefl _) (.eqRefl _) (multiply_distance P s qone G (num 8*(R*R)) D hD
      (uniform_bound f x C (halfIndex R K) hf) hs)
  have large : Γ ⊢[PRAAx] le G W := unit_monotone _ _ (by unfold C factorSize; ipra_le 32*𝔞 R*𝔞 R)
  exact distance_radius_mono _ _ _ _ _ _ hD hD
    (le_congr (by ipra_ring) (by unfold prefactorError; dsimp only [W]; ipra_ring)
      (le_mul_mono large (le_refl (num 8*(R*R)*D)))) raw

theorem t4_finite (f : PTm 2) (x s z R B K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hf : Γ ⊢[PRAAx] factorBounds f x (factorSize R) zero)
    (he : Γ ⊢[PRAAx] rowErrors f body x (pairT z B) (num 96*(R*R)) (R*R) (squareDenominator R K) K)
    (hs : Γ ⊢[PRAAx] distanceBounded s qone (num 8*(R*R)) (squareDenominator R K)) :
    Γ ⊢[PRAAx] distanceBounded (qmul s (qprod f (halfIndex R K) x)) (sineProduct z B K) (rate R) K :=
  absorb_errors _ _ _ R K _ hR hK (le_refl _) (prefactor_estimate f x s R K hf hs)
    (t6 f x z R B K hR hB hK hz hf he)

end LeanProofs.IPRA.Analysis.GaussianSineProductT6
