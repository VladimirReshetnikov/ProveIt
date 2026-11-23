import IPRADerivations.Analysis.GaussianEulerLogarithmicLowerFiniteBudget
import IPRADerivations.Analysis.GaussianEulerNamedLowerTail

/-!
# The original named logarithmic lower compact tail

The unchanged logarithmic compact name on [eta_q,eta_p] is compared with
the original transformed cofinal grid. Its source-only finite estimate
has exact leading coefficient j!(2A)^(j+1). One finite rational gap
removes the cofinal mesh and observation error while retaining only the
requested original compact observation error. Equal cutoffs are literal
zero-width observations of the same original program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicNamedLowerBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicLowerRootRows (panelExponent panelDegree intervalDen lipschitz fixedData)
open GaussianEulerLogarithmicCompactName (evaluatorF nameF)
open GaussianEulerLowerCofinalQuadrature (rootMesh transformed)
open GaussianEulerLowerTailPartition (totalWidth)
open GaussianEulerLowerTailRootGrid (timeNumerator timeDenominator)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianGammaIntegralCutoffs (height)
open GaussianCompactRiemannName (quadrature precision)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev source (z R B A : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B A
def data (j z R B p q A : PTm n) : PTm n := GaussianEulerLogarithmicCompactName.data j z R B (intervalDen q A R) one (lowerWidth p q (panelDegree A))
def point (s j z R B p q A : PTm n) : PTm n := ap2 nameF s (data j z R B p q A)
def leading (j A : PTm n) : PTm n := Products.fact j*pw (GaussianEulerLogarithmicLowerPointwise.degree A) (succ j)
def numerator (s j p A R : PTm n) : PTm n := leading j A*unit s+unit (height p (panelDegree A) R)
def denominator (s p A R : PTm n) : PTm n := unit (height p (panelDegree A) R)*unit s

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (j z R B p q A : PTm n) :
    Syn.subst σ (data j z R B p q A) = data (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) :=
  by simp [data,lowerWidth]
@[simp] theorem subst_point {m : ℕ} (σ : Fin n → PTm m) (s j z R B p q A : PTm n) :
    Syn.subst σ (point s j z R B p q A) = point (Syn.subst σ s) (Syn.subst σ j) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) := by simp [point]
@[simp] theorem subst_leading {m : ℕ} (σ : Fin n → PTm m) (j A : PTm n) :
    Syn.subst σ (leading j A) = leading (Syn.subst σ j) (Syn.subst σ A) := by simp [leading,Products.fact]

private theorem quadrature_congr (F : PR 3) (s N a C E N' a' C' E' x : PTm n)
    (hN : Γ ⊢[PRAAx] N ≐ N') (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E') : Γ ⊢[PRAAx]
    quadrature F s N a C E x ≐ quadrature F s N' a' C' E' x := by
  simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![s,N,a,C,E,x]) (σ' := ![s,N',a',C',E',x])
    (fun i => by fin_cases i; exact .eqRefl _; exact hN; exact ha; exact hC; exact hE; exact .eqRefl _)

theorem compact_input (j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF one (lowerWidth p q (panelDegree A)) (intervalDen q A R)
      (lipschitz j q A R) one (fixedData j z R B q A) := by
  have mod := GaussianEulerLogarithmicLowerRootRows.base_modulus j z R B p q A h hpq
  have ratioBound : Γ ⊢[PRAAx] le (GaussianGammaCompactCutoffGeometry.ratio p q (panelDegree A)) (intervalDen q A R) :=
    le_congr (one_mul _) ((mul_comm _ _).eqTrans
      (GaussianGammaCompactCutoffGeometry.eta_den_refinement p q (panelDegree A) R hpq).eqSymm)
      (mul_le_mul_right _ (GaussianGammaIntegralCutoffs.eta_den_positive p (panelDegree A) R))
  have endpoint : Γ ⊢[PRAAx] le (one+lowerWidth p q (panelDegree A)) (intervalDen q A R*one) :=
    le_congr (GaussianGammaCompactCutoffGeometry.lower_endpoint p q (panelDegree A)).eqSymm (by ipra_ring) ratioBound
  exact .andI (le_refl one) (.andI (GaussianGammaIntegralCutoffs.eta_den_positive q (panelDegree A) R)
    (.andI (le_trans (le_add_left _ _) endpoint) mod))

theorem name_regular (j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data j z R B p q A) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input j z R B p q A h hpq)

theorem cofinal_bound (t j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    bounded (transformed evaluatorF t (panelDegree A) (lowerWidth p q (panelDegree A)) (intervalDen q A R)
      (lipschitz j q A R) one (fixedData j z R B q A))
      (leading j A*unit t+GaussianEulerLogarithmicLowerFiniteBudget.residualCoefficient j p q A R*unit (height p (panelDegree A) R))
      (unit (height p (panelDegree A) R)*unit t) := by
  let D := panelDegree A
  let L := lipschitz j q A R
  let H := rootMesh t L one
  let s := precision t one
  let x := fixedData j z R B q A
  have hH := GaussianEulerLowerCofinalQuadrature.root_mesh_positive (Γ := Γ) t L one
  have meshBudget : Γ ⊢[PRAAx] le (unit t) H :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L one))
  have precisionBudget : Γ ⊢[PRAAx] le (unit t) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right t one) (le_add_right _ _))
  have finite := GaussianEulerLogarithmicLowerFiniteBudget.original_finite_budget s t j z R B H p q A
    (.andI h (.andI hH hpq)) meshBudget precisionBudget
  have actual : Γ ⊢[PRAAx] GaussianEulerLogarithmicLowerQuadrature.originalQuadrature s j z R B H p q A ≐
      transformed evaluatorF t D (lowerWidth p q D) (intervalDen q A R) L one x :=
    quadrature_congr evaluatorF s _ _ _ _ _ _ _ _ x (GaussianEulerLowerTailRootGrid.time_width H p q D)
      (GaussianEulerLowerTailRootGrid.time_first H p q D) (GaussianEulerLowerTailRootGrid.time_width H p q D)
      (GaussianEulerLowerTailRootGrid.time_denominator H q D R)
  have num : Γ ⊢[PRAAx] GaussianEulerLogarithmicLowerFiniteBudget.numerator t j p q A R ≐
      leading j A*unit t+GaussianEulerLogarithmicLowerFiniteBudget.residualCoefficient j p q A R*unit (height p D R) := by
    have e := natEq (GaussianEulerLogarithmicLowerFiniteBudget.leading_coefficient (Γ := Γ) j A h.andE₁)
    dsimp only [panelDegree] at e
    apply deriveNat
    unfold GaussianEulerLogarithmicLowerFiniteBudget.numerator GaussianEulerLowerTailFiniteBudget.numerator
      GaussianEulerLowerTailFiniteBudget.nativeNumerator GaussianEulerLogarithmicLowerFiniteBudget.residualCoefficient leading
    dsimp only [D,panelDegree]
    ipra_simps
    linear_combination (Groth.ι (Q.mk Γ (unit t)))*e
  exact bound_congr actual num (.eqRefl _) finite

theorem original_slack (s t j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point s j z R B p q A) (numerator s j p A R) (denominator s p A R)
      (GaussianEulerLogarithmicLowerFiniteBudget.residualCoefficient j p q A R+two) t := by
  have hC := GaussianGammaCompactCutoffGeometry.lower_positive p q (panelDegree A) (zero_lt_succ _) hpq
  have observations := GaussianEulerLowerCofinalQuadrature.observations evaluatorF t s (panelDegree A)
    (lowerWidth p q (panelDegree A)) (intervalDen q A R) (lipschitz j q A R) one (fixedData j z R B q A)
    (.andI (zero_lt_succ _) (.andI hC (compact_input j z R B p q A h (le_of_lt hpq))))
  have near := distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at evaluatorF s one _ _ _ _ _).eqSymm
    (.eqRefl _) (.eqRefl _) observations
  exact GaussianEulerNamedLowerTail.compared_bound_to_slack _ _ (leading j A) (unit (height p (panelDegree A) R)) _ s t (unit_positive _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive s)) near) (cofinal_bound t j z R B p q A h hpq)

theorem strict_bound (s j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    bounded (point s j z R B p q A) (numerator s j p A R) (denominator s p A R) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (GaussianEulerLogarithmicLowerFiniteBudget.residualCoefficient j p q A R+two)
    (positive_product _ _ (unit_positive _) (unit_positive s)) (original_slack s _ j z R B p q A h hpq)

theorem equal_bound (s j z R B p q A : PTm n) (hpq : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    bounded (point s j z R B p q A) (numerator s j p A R) (denominator s p A R) := by
  have widths : Γ ⊢[PRAAx] lowerWidth p q (panelDegree A) ≐ lowerWidth p p (panelDegree A) := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (lowerWidth (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![p,q,panelDegree A]) (σ' := ![p,p,panelDegree A])
      (fun i => by fin_cases i; exact .eqRefl _; exact hpq.eqSymm; exact .eqRefl _)
  have width := widths.eqTrans (GaussianGammaCompactCutoffGeometry.same_lower p (panelDegree A))
  have actual : Γ ⊢[PRAAx] point s j z R B p q A ≐ qzero := by
    have read := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF s one (lowerWidth p q (panelDegree A)) (intervalDen q A R)
      (lipschitz j q A R) one (fixedData j z R B q A)
    have switched := Prf.eqCongr1 (Γ := Γ) (GaussianCompactRiemannName.sample evaluatorF (Syn.shift s) one (var 0)
      (Syn.shift (intervalDen q A R)) (Syn.shift (lipschitz j q A R)) one (Syn.shift (fixedData j z R B q A))) width
    have widthChange : Γ ⊢[PRAAx] GaussianCompactRiemannName.sample evaluatorF s one (lowerWidth p q (panelDegree A)) (intervalDen q A R)
        (lipschitz j q A R) one (fixedData j z R B q A) ≐
        GaussianCompactRiemannName.sample evaluatorF s one zero (intervalDen q A R) (lipschitz j q A R) one (fixedData j z R B q A) :=
      by simpa using switched
    exact read.eqTrans (widthChange.eqTrans
      (GaussianCompactZeroWidth.sample_zero evaluatorF s one _ _ _ _ (GaussianGammaIntegralCutoffs.eta_den_positive q (panelDegree A) R)))
  exact bound_congr actual.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerNamedUpperTail.zero_bound _ _ (positive_product _ _ (unit_positive _) (unit_positive s)))

theorem original_named_bound (s j z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    bounded (point s j z R B p q A) (numerator s j p A R) (denominator s p A R) :=
  .orE (lt_or_eq_of_le hpq) (strict_bound s j z R B p q A h.wk Prf.hyp0) (equal_bound s j z R B p q A Prf.hyp0)

theorem original_named_logarithmic_lower_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 2) (var 3) (var 4) (var 7) ⋏ le (var 5) (var 6)) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (numerator (var 0) (var 1) (var 5) (var 7) (var 3)) (denominator (var 0) (var 5) (var 7) (var 3))) :=
  closeUniv 8 (.impI (original_named_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicNamedLowerBound
