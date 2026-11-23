import IPRADerivations.Analysis.GaussianEulerLogarithmicLowerRootRows
import IPRADerivations.Analysis.GaussianScaledLowerRootQuadrature

/-!
# Actual finite logarithmic Euler quadrature near zero

Every original affine grid observation is compared with its actual
right transformed endpoint. The fixed compact logarithmic modulus and
the source-only factorial endpoint bound discharge the scaled old block
contract. The literal old partition, Gaussian finite sums and weight give
the complete finite quadrature bound, with all mesh and observation errors
explicit. No named lower-tail or derivative law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerQuadrature

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicLowerRootRows (source panelExponent panelDegree intervalDen lipschitz fixedData)
open GaussianEulerLogarithmicLowerPointwise (coefficient)
open GaussianEulerLogarithmicCompactName (evaluatorF)
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator)
open GaussianEulerLowerTailPartition (panelWidth totalWidth)
open GaussianEulerLowerTailRowBound (stepScale)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem subst_rootDenominator {m : ℕ} (σ : Fin n → PTm m) (H q A R : PTm n) :
    Syn.subst σ (rootDenominator H q A R) = rootDenominator (Syn.subst σ H) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) :=
  by simp [rootDenominator,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
private theorem subst_rootNumerator {m : ℕ} (σ : Fin n → PTm m) (i H p q : PTm n) :
    Syn.subst σ (rootNumerator i H p q) = rootNumerator (Syn.subst σ i) (Syn.subst σ H) (Syn.subst σ p) (Syn.subst σ q) :=
  by simp [rootNumerator,GaussianEulerLowerTailRootGrid.rootRatio]
attribute [local simp] subst_rootDenominator subst_rootNumerator

def originalQuadrature (s j z R B H p q A : PTm n) : PTm n :=
  GaussianScaledLowerRootQuadrature.originalQuadrature evaluatorF s H p q (panelExponent A) R (fixedData j z R B q A)

theorem scaled_local_row (x y C D U V S L P : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hD : Γ ⊢[PRAAx] le one D)
    (hV : Γ ⊢[PRAAx] le one V) (hP : Γ ⊢[PRAAx] le one P)
    (near : Γ ⊢[PRAAx] distanceBounded x y (L*S*P+two*D) (D*P))
    (right : Γ ⊢[PRAAx] bounded y (C*U*P+V) (V*P)) : Γ ⊢[PRAAx]
    bounded x (C*GaussianEulerLowerBlockWeight.rowNumerator D U V S L P)
      (GaussianEulerLowerBlockWeight.rowDenominator D V P) := by
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ hD hP) (positive_product _ _ hV hP) near right
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hD hP) (positive_product _ _ hV hP))
    (GaussianEulerLowerBlockWeight.row_denominator_positive D V P hD hV hP) _ raw
  unfold GaussianEulerLowerBlockWeight.rowNumerator GaussianEulerLowerBlockWeight.rowDenominator
  ipra_le (𝔞 V*𝔞 D*𝔞 V*𝔞 P^2*(𝔞 L*𝔞 S*𝔞 P+3*𝔞 D))*sl hC

theorem width_positive (H p q A : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    le one (totalWidth H p q (panelDegree A)) :=
  le_congr (.eqRefl _) (GaussianEulerLowerTailRootGrid.time_width H p q (panelDegree A)).eqSymm
    (positive_product _ _ (GaussianGammaCompactCutoffGeometry.lower_positive p q (panelDegree A) (zero_lt_succ _) hpq)
      (GaussianPolynomialPerturbation.power_positive H (panelDegree A) hH))

theorem actual_row_norm_bound (i u s j z R B H p q A : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i H)
    (hu : Γ ⊢[PRAAx] lt u (panelWidth i H p q (panelDegree A)))
    (hW : Γ ⊢[PRAAx] le one (totalWidth H p q (panelDegree A)))
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (GaussianEulerLowerTailLocalComparison.rowTime i u H p q (panelDegree A) R) (fixedData j z R B q A))
      (coefficient j A*GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator H q (panelDegree A) R)
        (pw (rootDenominator H q (panelDegree A) R) (panelExponent A))
        (pw (rootNumerator (succ i) H p q) (panelExponent A)) (stepScale p q (panelExponent A)) (lipschitz j q A R) (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator H q (panelDegree A) R)
        (pw (rootNumerator (succ i) H p q) (panelExponent A)) (unit s)) := by
  let e := panelExponent A
  let D := rootDenominator H q (panelDegree A) R
  let V := pw (rootNumerator (succ i) H p q) e
  have hD := positive_product (Γ := Γ) _ _ (unit_positive (GaussianGammaIntegralCutoffs.height q (panelDegree A) R)) hH
  have hV := GaussianPolynomialPerturbation.power_positive (Γ := Γ) _ e
    (GaussianEulerLowerTailPartition.root_right_guard i H p q (panelDegree A) R hH hpq hi).andE₁
  have est := GaussianEulerLowerTailLocalComparison.original_row_distance evaluatorF i u H p q e R (lipschitz j q A R)
    (fixedData j z R B q A) s s hH hpq hi hu hW (GaussianEulerLogarithmicLowerRootRows.root_modulus j z R B H p q A h hH hpq)
  have near := GaussianEulerLowerTailRowBound.scale_local_budget _ _ s H p q e R (lipschitz j q A R) hH est
  exact scaled_local_row _ _ (coefficient j A) D _ V _ _ (unit s)
    (GaussianEulerLogarithmicLowerPointwise.coefficient_positive j A h.andE₁) hD hV (unit_positive s) near
    (GaussianEulerLogarithmicLowerRootRows.original_right_observation_bound i s j z R B H p q A h hH hpq hi)

theorem original_panel_rows (i s j z R B H p q A : PTm n) (hi : Γ ⊢[PRAAx] lt i H)
    (h : Γ ⊢[PRAAx] source z R B H p q A) : Γ ⊢[PRAAx]
    GaussianUniformFiniteSumBound.summandsBounded (offB (GaussianCompactRiemannName.sampleBody evaluatorF)) (panelWidth i H p q (panelDegree A))
      (pairT (GaussianEulerLowerTailPartition.offset i H p q (panelDegree A))
        (GaussianScaledLowerRootQuadrature.gridData s H p q (panelExponent A) R (fixedData j z R B q A)))
      (coefficient j A*GaussianEulerLowerBlockWeight.rowNumerator (rootDenominator H q (panelDegree A) R)
        (pw (rootDenominator H q (panelDegree A) R) (panelExponent A))
        (pw (rootNumerator (succ i) H p q) (panelExponent A)) (stepScale p q (panelExponent A)) (lipschitz j q A R) (unit s))
      (GaussianEulerLowerBlockWeight.rowDenominator (rootDenominator H q (panelDegree A) R)
        (pw (rootNumerator (succ i) H p q) (panelExponent A)) (unit s)) := by
  refine .allI (.impI ?_)
  have hi' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift i) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hi.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift A) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  let Δ := lt (var 0) (Syn.shift (panelWidth i H p q (panelDegree A))) :: Γ.map Fm.shift
  have hu : Δ ⊢[PRAAx] lt (var 0) (panelWidth (Syn.shift i) (Syn.shift H) (Syn.shift p) (Syn.shift q) (panelDegree (Syn.shift A))) := by
    simpa [Δ,Syn.shift,panelWidth,panelDegree] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (panelWidth i H p q (panelDegree A))))
  have hW := width_positive (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift A) hs.andE₂.andE₁ hs.andE₂.andE₂
  have bound := actual_row_norm_bound (Γ := Δ) (Syn.shift i) (var 0) (Syn.shift s) (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift A) hs.andE₂.andE₁.wk (le_of_lt hs.andE₂.andE₂).wk hi'.wk hu hW.wk hs.andE₁.wk
  have actual := GaussianScaledLowerRootQuadrature.literal_panel_row (Γ := Δ) evaluatorF (Syn.shift i) (var 0) (Syn.shift s)
    (Syn.shift H) (Syn.shift p) (Syn.shift q) (panelExponent (Syn.shift A)) (Syn.shift R)
    (fixedData (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift q) (Syn.shift A))
  simpa [Δ,GaussianUniformFiniteSumBound.summandsBounded,panelWidth,panelDegree,stepScale,Syn.shift] using
    bound_congr actual.eqSymm (.eqRefl _) (.eqRefl _) bound

theorem generic_source (s j z R B H p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B H p q A) : Γ ⊢[PRAAx]
    GaussianScaledLowerRootQuadrature.source evaluatorF s H p q (panelExponent A) R (lipschitz j q A R)
      (coefficient j A) (fixedData j z R B q A) := by
  have rows : Γ ⊢[PRAAx] GaussianScaledLowerRootQuadrature.panelRows evaluatorF s H p q (panelExponent A) R (lipschitz j q A R)
      (coefficient j A) (fixedData j z R B q A) := by
    refine .allI (.impI ?_)
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift A) :=
      by simpa [Fm.shift,Syn.shift] using h.shift
    simpa [GaussianScaledLowerRootQuadrature.panelRows,panelDegree,Syn.shift] using
      original_panel_rows (var 0) (Syn.shift s) (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B)
        (Syn.shift H) (Syn.shift p) (Syn.shift q) (Syn.shift A) Prf.hyp0 hs.wk
  exact .andI h.andE₂.andE₁ (.andI (le_of_lt h.andE₂.andE₂) (.andI (width_positive H p q A h.andE₂.andE₁ h.andE₂.andE₂) rows))

theorem original_finite_lower_quadrature_bound (s j z R B H p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B H p q A) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s j z R B H p q A)
      (H*(coefficient j A*GaussianEulerLowerBlockWeight.numerator (rootDenominator H q (panelDegree A) R)
        (stepScale p q (panelExponent A)) (lipschitz j q A R) (unit s)))
      (GaussianEulerLowerBlockWeight.denominator (rootDenominator H q (panelDegree A) R) (unit s)) :=
  GaussianScaledLowerRootQuadrature.finite_bound evaluatorF s H p q (panelExponent A) R (lipschitz j q A R)
    (coefficient j A) (fixedData j z R B q A) (generic_source s j z R B H p q A h)

theorem original_logarithmic_lower_finite_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      bounded (originalQuadrature (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (var 5*(coefficient (var 1) (var 8)*GaussianEulerLowerBlockWeight.numerator
          (rootDenominator (var 5) (var 7) (panelDegree (var 8)) (var 3)) (stepScale (var 6) (var 7) (panelExponent (var 8)))
          (lipschitz (var 1) (var 7) (var 8) (var 3)) (unit (var 0))))
        (GaussianEulerLowerBlockWeight.denominator (rootDenominator (var 5) (var 7) (panelDegree (var 8)) (var 3)) (unit (var 0)))) :=
  closeUniv 9 (.impI (original_finite_lower_quadrature_bound _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerQuadrature
