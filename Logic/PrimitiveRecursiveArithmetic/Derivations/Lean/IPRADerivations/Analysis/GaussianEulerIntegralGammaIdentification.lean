import IPRADerivations.Analysis.GaussianBetaFiniteEulerAtCutoff
import IPRADerivations.Analysis.GaussianBetaFiniteGammaComparison
import IPRADerivations.Analysis.GaussianBetaFixedCutoffSplit
import IPRADerivations.Analysis.GaussianBetaRefinedFixedCompactBudget
import IPRADerivations.Analysis.GaussianBetaUpperTailDyadic
import IPRADerivations.Analysis.GaussianEulerLaterCutoffObservation
import IPRADerivations.Analysis.GaussianGammaEulerInverseApproximationName

/-!
# The original improper Euler integral equals Gamma at encoded rational inputs

Use one original positive cutoff on both sides. Choose the finite beta
degree only after that cutoff. A shared mesh splits the actual finite
beta quadrature into the compact middle and a small upper tail. The
same whole beta quadrature approximates the original finite Euler
reciprocal and then the original Gamma name by C15. Removing the
auxiliary observation errors proves equivalence of the original two
regular names at independent precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegralGammaIdentification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianRationalHorner (qadd qmul_canonical positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianBetaFiniteEulerComparison (slack)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ le one R
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    (source z R B A).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [source]

def cutoff (t A : PTm n) : PTm n := t+GaussianBetaFiniteEulerAtCutoff.minimumCutoff (slack t) A
def degree (t k A R : PTm n) : PTm n :=
  GaussianBetaFiniteGammaComparison.minimumDegree t R A+GaussianBetaRefinedFixedCompactBudget.minimumDegree t k A R
def meshFactor (t k z R B A N : PTm n) : PTm n :=
  GaussianBetaFiniteEulerAtCutoff.minimumCells (slack t) k z R B A N+GaussianBetaUpperTailDyadic.minimumMesh t R N+one
def evaluationPrecision (t q k z R B A N M : PTm n) : PTm n :=
  GaussianBetaFiniteEulerAtCutoff.minimumPrecision (slack t) k z R B A N M+
    GaussianBetaRefinedFixedCompactBudget.minimumPrecision t q k A R+
    GaussianBetaUpperTailDyadic.minimumPrecision t R N+
    GaussianFastValueCut.exponent (two*N) t

theorem improper_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] GaussianEulerImproperName.source z R B A :=
  .andI h.andE₁.andE₂.andE₁ h.andE₁

theorem original_diagonal_observations (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data z R B A))
      (ap2 gammaF t (gammaData z R B A)) (num 7) (unit t) := by
  let j := slack t
  let q := succ t
  let k := cutoff t A
  let E := etaDen k A R
  let N₁ := GaussianBetaFiniteGammaComparison.minimumDegree t R A
  let N₂ := GaussianBetaRefinedFixedCompactBudget.minimumDegree t k A R
  let N := degree t k A R
  let F₁ := GaussianBetaFiniteEulerAtCutoff.minimumCells j k z R B A N
  let F₂ := GaussianBetaUpperTailDyadic.minimumMesh t R N
  let F := meshFactor t k z R B A N
  let S := GaussianBetaFixedCutoffSplit.commonMultiplier q k A R F
  let C := GaussianBetaFixedCutoffSplit.fullWidth k A R N
  let O := GaussianBetaFixedCutoffSplit.upperWidth k A R N
  let M := C*S
  let P₁ := GaussianBetaFiniteEulerAtCutoff.minimumPrecision j k z R B A N M
  let P₂ := GaussianBetaRefinedFixedCompactBudget.minimumPrecision t q k A R
  let P₃ := GaussianBetaUpperTailDyadic.minimumPrecision t R N
  let P₄ := GaussianFastValueCut.exponent (two*N) t
  let P₅ := GaussianBetaRefinedFixedCompactComparison.referencePrecision q k A R
  let p := evaluationPrecision t q k z R B A N M
  let I := ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data z R B A)
  let Q := GaussianBetaRefinedFixedCompactComparison.compactObservation q z R B k A
  let W := GaussianBetaFixedCutoffSplit.middle p z B k A R N S
  let T := GaussianBetaFixedCutoffSplit.upper p z B k A R N S
  let V := GaussianBetaFixedCutoffSplit.full p z B k A R N S
  let G := ap2 gammaF t (gammaData z R B A)
  have hu := unit_positive (Γ := Γ) t
  have hj := unit_positive (Γ := Γ) j
  have he : Γ ⊢[PRAAx] le one E := eta_den_positive k A R
  have hk0 : Γ ⊢[PRAAx] le t k := le_add_right _ _
  have hk1 : Γ ⊢[PRAAx] le (GaussianBetaFiniteEulerAtCutoff.minimumCutoff j A) k := le_add_left _ _
  have hn1 : Γ ⊢[PRAAx] le N₁ N := le_add_right _ _
  have hn2 : Γ ⊢[PRAAx] le N₂ N := le_add_left _ _
  have anchor : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B := h.andE₁.andE₂.andE₁
  have hnTop : Γ ⊢[PRAAx] le (two*GaussianGammaIntegralCutoffs.top k A R) N := by
    have first : Γ ⊢[PRAAx] le (two*GaussianGammaIntegralCutoffs.top k A R) N₂ := by
      apply le_of_eq_add (d := one+num 4*GaussianBetaRefinedFixedCompactBudget.degreeCost k A R*unit t)
      unfold N₂ GaussianBetaRefinedFixedCompactBudget.minimumDegree
      ipra_ring
    exact le_trans first hn2
  have degreeInfo := GaussianBetaFiniteGammaComparison.degree_budgets t R A N hn1
  have hFinite : Γ ⊢[PRAAx] GaussianBetaFiniteEulerComparison.source z R B A N :=
    .andI h.andE₁ (.andI h.andE₂ degreeInfo.andE₁)
  have hn := GaussianBetaFiniteEulerComparison.degree_positive z R B A N hFinite
  have hf : Γ ⊢[PRAAx] le one F := le_add_left _ _
  have hs : Γ ⊢[PRAAx] le one S := GaussianBetaFixedCutoffSplit.common_multiplier_positive q k A R F hf
  have fToS : Γ ⊢[PRAAx] le F S :=
    le_congr (one_mul F) (.eqRefl _)
      (mul_le_mul_right F (GaussianCompactRiemannName.mesh_positive (Γ := Γ) _ _ _))
  have p1 : Γ ⊢[PRAAx] le P₁ p :=
    le_of_eq_add (d := P₂+P₃+P₄) (by change _ ⊢[PRAAx] P₁+P₂+P₃+P₄ ≐ P₁+(P₂+P₃+P₄); ipra_ring)
  have p2 : Γ ⊢[PRAAx] le P₂ p :=
    le_of_eq_add (d := P₁+P₃+P₄) (by change _ ⊢[PRAAx] P₁+P₂+P₃+P₄ ≐ P₂+(P₁+P₃+P₄); ipra_ring)
  have p3 : Γ ⊢[PRAAx] le P₃ p :=
    le_of_eq_add (d := P₁+P₂+P₄) (by change _ ⊢[PRAAx] P₁+P₂+P₃+P₄ ≐ P₃+(P₁+P₂+P₄); ipra_ring)
  have p4 : Γ ⊢[PRAAx] le P₄ p := le_add_left _ _
  have p5 : Γ ⊢[PRAAx] le P₅ p := le_trans (le_add_right _ _) p2
  have hMiddle : Γ ⊢[PRAAx] GaussianBetaRefinedFixedCompactComparison.source p q F z R B k A N :=
    .andI anchor (.andI hf (.andI p5 (.andI hn hnTop)))
  have hSplit := GaussianBetaFixedCutoffSplit.source_from_middle_comparison p q F z R B k A N hMiddle
  have cPos := GaussianBetaFixedCutoffSplit.full_width_positive k A R N (le_of_lt hSplit.andE₂.andE₁)
  have hm : Γ ⊢[PRAAx] le F₁ M :=
    le_trans (le_trans (le_add_right F₁ F₂) (le_add_right _ _))
      (le_trans fToS (le_congr (one_mul S) (.eqRefl _) (mul_le_mul_right S cPos)))
  have hTail : Γ ⊢[PRAAx] GaussianBetaUpperTailDyadic.source z R B k A O E N S :=
    .andI anchor (.andI hn (.andI (GaussianBetaFixedCutoffSplit.upper_width_positive k A R N hSplit.andE₂.andE₁)
      (.andI he (.andI hs (le_congr
        (GaussianBetaFixedCutoffSplit.exact_upper_tail_endpoint k A R N (le_of_lt hSplit.andE₂.andE₁)).eqSymm
        (.eqRefl _) (le_refl _))))))
  have tailMesh : Γ ⊢[PRAAx] le F₂ S := le_trans (le_trans (le_add_left F₂ F₁) (le_add_right _ _)) fToS
  have tail : Γ ⊢[PRAAx] bounded T one (unit t) :=
    GaussianBetaUpperTailDyadic.dyadic_upper_bound t p k A R O E z B N S hTail hk0 tailMesh p3
  have splitBudget : Γ ⊢[PRAAx] le ((two*N)*unit t) (one*unit p) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm
      (le_trans (GaussianFastValueCut.query_budget (two*N) t) (GaussianExponentialReference.unit_monotone p4))
  have split : Γ ⊢[PRAAx] distanceBounded V (qadd W T) one (unit t) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive p) hu splitBudget
      (GaussianBetaFixedCutoffSplit.original_coarse_split p z R B k A N S hSplit)
  have tailCanonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical T := qmul_canonical _ _
  have dropTail : Γ ⊢[PRAAx] distanceBounded (qadd W T) W one (unit t) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalSyntheticDivision.qadd_sub_cancel W T tailCanonical).eqSymm
      (.eqRefl _) (.eqRefl _) tail
  have fullMiddle : Γ ⊢[PRAAx] distanceBounded W V two (unit t) :=
    distance_symmetric _ _ _ _ hu
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
        (distance_triangle_same _ _ _ _ _ _ hu split dropTail))
  have refPos : Γ ⊢[PRAAx] le one (GaussianBetaFixedCutoffSplit.middleFactor k A R F) :=
    positive_product _ _ (GaussianGammaCompactCutoffGeometry.width_positive _ _ _) hf
  have middle : Γ ⊢[PRAAx] distanceBounded Q W one (unit t) :=
    distance_symmetric _ _ _ _ hu
      (distance_congr (GaussianBetaFixedCutoffSplit.middle_is_original_refined_beta p q F z R B k A N).eqSymm
        (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (GaussianBetaRefinedFixedCompactBudget.original_refined_middle_dyadic p q t
          (GaussianBetaFixedCutoffSplit.middleFactor k A R F) z R B k A N anchor refPos (le_succ_self t) hn2 p2))
  have atCutoff := GaussianEulerLaterCutoffObservation.later_cutoff_observations t q t z R B A k
    (improper_source z R B A h) hk0 (le_refl _)
  have first : Γ ⊢[PRAAx] distanceBounded I Q two (unit t) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by ipra_ring)) atCutoff
  have atInverse := GaussianBetaFiniteEulerAtCutoff.original_at_cutoff j p j k z R B A N M hFinite hk1 hm p1
  have near : Γ ⊢[PRAAx] distanceBounded V (ap2 GaussianGammaEulerReciprocalInverse.eulerF j
        (GaussianGammaEulerReciprocalInverse.eulerData z R B A N)) two (unit j) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hj hj) hj
      (le_of_eq_add (d := zero) (by ipra_ring)) atInverse
  have gamma := GaussianBetaFiniteGammaComparison.from_finite_euler_error t t z R B A N V h hn1 near
  have last : Γ ⊢[PRAAx] distanceBounded V G two (unit t) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by ipra_ring)) gamma
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same I Q G two (one+(two+two)) (unit t) hu first
      (distance_triangle_same Q W G one (two+two) (unit t) hu middle
        (distance_triangle_same W V G two two (unit t) hu fullMiddle last)))

theorem original_gamma_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] pointCN gammaF (gammaData z R B A) :=
  GaussianGammaReciprocalInverse.gamma_regular z R B one A
    (GaussianGammaRightHalfPlane.original_right_half_plane_source z R B A
      (.andI h.andE₂ h.andE₁.andE₂.andE₁) h.andE₁.andE₁ h.andE₁.andE₂.andE₂)

theorem original_Euler_integral_is_Gamma (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent GaussianEulerImproperName.nameF gammaF
      (GaussianEulerImproperName.data z R B A) (gammaData z R B A) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 7)
    (GaussianEulerImproperName.name_regular z R B A (improper_source z R B A h))
    (original_gamma_regular z R B A h)
  refine .allI ?_
  have shifted : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) := by
    simpa only [Fm.shift, Syn.shift, subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift,
    GaussianEulerImproperName.subst_data, GaussianGammaEulerInverseApproximationName.subst_gammaData,
    LeanProofs.IPRA.PTm.subst_num] using
      original_diagonal_observations (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) shifted

theorem original_encoded_right_half_plane_Euler_integral_is_Gamma_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶
        crossEquivalent GaussianEulerImproperName.nameF gammaF
          (GaussianEulerImproperName.data (var 0) (var 1) (var 2) (var 3))
          (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_Euler_integral_is_Gamma _ _ _ _ Prf.hyp0))

theorem original_encoded_Euler_and_Gamma_independent_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 2) (var 3) (var 4) (var 5) ⟶
        distanceBounded
          (ap2 GaussianEulerImproperName.nameF (var 0) (GaussianEulerImproperName.data (var 2) (var 3) (var 4) (var 5)))
          (ap2 gammaF (var 1) (gammaData (var 2) (var 3) (var 4) (var 5)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (GaussianNameEquivalence.cross_at _ _ _ _ _ _ (original_Euler_integral_is_Gamma _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegralGammaIdentification
