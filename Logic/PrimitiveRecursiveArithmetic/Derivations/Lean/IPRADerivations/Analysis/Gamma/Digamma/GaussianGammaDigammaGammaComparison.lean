import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaConvexComparison
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaExponentialOrder
import IPRADerivations.Analysis.Stirling.GaussianStirlingLogDuplication

/-!
# Equal-step multiplicative comparison of native Gamma values

Exponentiating the complementary convex comparison yields the exact
order Γ(x+1/D) Γ(y) ≤ Γ(x) Γ(y+1/D) for positive rationals x≤y.
Both sides use the original reciprocal-derived Gamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaGammaComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaDigammaConvexComparison (innerData outerData log_comparison inner_regular outer_regular)
open GaussianGammaDigammaStep (neighborNumerator neighborDenominator neighborData neighbor_source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianRadiusExponentialName (nameF data)
open GaussianStirlingGammaLogarithm (source gammaData gamma_regular logGammaF logGammaData log_gamma_regular)
open GaussianStirlingLogDuplication (exponential_sum exponential_gamma exponential_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LF" => GaussianGammaDigammaConvexComparison.sumF

def productF : PR 2 := multiplyF gammaF gammaF
def innerProductData (a c b D : PTm n) : PTm n := multiplyData gammaF gammaF (neighborData a b D) (gammaData c b)
def outerProductData (a c b D : PTm n) : PTm n := multiplyData gammaF gammaF (gammaData a b) (neighborData c b D)

@[simp] theorem subst_innerProductData {m : ℕ} (σ : Fin n → PTm m) (a c b D : PTm n) :
    Syn.subst σ (innerProductData a c b D) =
      innerProductData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [innerProductData,neighborData,neighborNumerator,neighborDenominator]

@[simp] theorem subst_outerProductData {m : ℕ} (σ : Fin n → PTm m) (a c b D : PTm n) :
    Syn.subst σ (outerProductData a c b D) =
      outerProductData (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [outerProductData,neighborData,neighborNumerator,neighborDenominator]

set_option maxHeartbeats 800000 in
theorem product_from_exp (a b c d R : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c d)
    (hR : Γ ⊢[PRAAx] le (U LF (GaussianNameArithmetic.addData (logGammaData a b) (logGammaData c d))) R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF LF) productF
      (data R (GaussianNameArithmetic.addData (logGammaData a b) (logGammaData c d)))
      (multiplyData gammaF gammaF (gammaData a b) (gammaData c d)) := by
  let x := logGammaData a b
  let y := logGammaData c d
  let s := GaussianNameArithmetic.addData x y
  let t := U LF s
  let F := nameF logGammaF
  have hx := log_gamma_regular a b ha
  have hy := log_gamma_regular c d hc
  have sum := GaussianNameArithmetic.add_fast logGammaF logGammaF x y hx hy
  have inp := GaussianGammaFiniteApproximantName.exponential_input LF s sum
  have widen := GaussianExponentialRadiusIndependence.input_widen LF t R s inp hR
  have radii := GaussianExponentialRadiusIndependence.same_input_cross LF R t s widen inp
  have prod := multiply_cross F gammaF F gammaF (data (U logGammaF x) x) (gammaData a b)
    (data (U logGammaF y) y) (gammaData c d) (exponential_regular _ _ hx) (gamma_regular _ _ ha)
    (exponential_regular _ _ hy) (gamma_regular _ _ hc) (exponential_gamma a b ha) (exponential_gamma c d hc)
  exact cross_trans _ _ _ _ _ _ radii (cross_trans _ _ _ _ _ _
    (cross_symm _ _ _ _ (exponential_sum logGammaF logGammaF x y hx hy)) prod)

set_option maxHeartbeats 800000 in
theorem gamma_comparison (a c b D : PTm n) (ha : Γ ⊢[PRAAx] source a b) (hc : Γ ⊢[PRAAx] source c b)
    (hac : Γ ⊢[PRAAx] le a c) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] realOrder productF productF (innerProductData a c b D) (outerProductData a c b D) := by
  let x := innerData a c b D
  let y := outerData a c b D
  let B := neighborDenominator b D
  let α := neighborNumerator a b D
  let γ := neighborNumerator c b D
  let R := GaussianGammaDigammaExponentialOrder.radius LF LF x y
  have hx := inner_regular a c b D ha hc hD
  have hy := outer_regular a c b D ha hc hD
  have fx := GaussianStirlingNames.add_real (Γ := Γ) _ _ _ _ (GaussianStirlingNames.log_gamma_real α B)
    (GaussianStirlingNames.log_gamma_real c b)
  have fy := GaussianStirlingNames.add_real (Γ := Γ) _ _ _ _ (GaussianStirlingNames.log_gamma_real a b)
    (GaussianStirlingNames.log_gamma_real γ B)
  have order := GaussianGammaDigammaExponentialOrder.exp_order LF LF x y hx hy fx fy (log_comparison a c b D ha hc hac hD)
  have left := product_from_exp α B c b R (neighbor_source a b D ha hD) hc (le_add_right _ _)
  have right := product_from_exp a b γ B R ha (neighbor_source c b D hc hD)
    (le_trans (le_add_right _ _) (le_add_left _ _))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right order

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaGammaComparison
