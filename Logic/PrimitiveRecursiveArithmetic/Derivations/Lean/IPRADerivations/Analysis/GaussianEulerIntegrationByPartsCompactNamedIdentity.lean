import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsCompactNameObservations
import IPRADerivations.Analysis.GaussianCompactZeroWidth
import IPRADerivations.Core.CongruenceTactic

/-!
# Original regular compact Euler integration by parts

A source-derived refined grid connects the two actual normalized names.
Both true endpoint names retain their nonzero values. All temporary
errors have a fixed coefficient depending only on the compact input;
the existing finite-gap envelope theorem removes it at independent
requested observations. Zero-width intervals are handled separately.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNamedIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrationByPartsCompactNames
open GaussianEulerIntegrationByPartsCompactNameObservations (rawLeft left_readback boundary_readback boundary_query_error grid_to_compact)
open GaussianGammaEulerHeadShift (shifted)
open GaussianRationalHorner (ofGaussian qmul qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (z R B a C E T : PTm n) : PTm n := productModulus z R B a C E T+R+num 21
@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    Syn.subst σ (gain z R B a C E T) = gain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [gain]

theorem positive_diagonal (t z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 leftF t (leftData z R B a C E T)) (ap2 boundaryF t (boundaryData z B a C E))
      (gain z R B a C E T) (unit t) := by
  let S := R+one
  let H := GaussianEulerIntegrationByPartsGridBudget.minimumMesh t S E T C
  let M := GaussianCompactRiemannName.mesh t (GaussianEulerCompactModulus.lipschitz S E T) T
  let N := H*M
  let P₀ := GaussianEulerIntegrationByPartsCompact.minimumObservation t S E T N
  let P₁ := GaussianCompactRiemannName.precision t T
  let p := P₀+P₁+t
  let Q := GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (GaussianEulerIntegrandName.fixedData z B)
  let Q' := GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF p N a C E (GaussianEulerIntegrandName.fixedData (shifted z B) B)
  have both := common_sources z R B a C E T h
  have hH : Γ ⊢[PRAAx] le one H := le_trans (le_add_right _ _) (le_add_right _ _)
  have hM : Γ ⊢[PRAAx] le one M := GaussianCompactRiemannName.mesh_positive _ _ _
  have hm : Γ ⊢[PRAAx] le H N := le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl H) hM)
  have hp0 : Γ ⊢[PRAAx] le P₀ p := le_trans (le_add_right _ _) (le_add_right _ _)
  have hp1 : Γ ⊢[PRAAx] le P₁ p := le_trans (le_add_left _ _) (le_add_right _ _)
  have hpt : Γ ⊢[PRAAx] le t p := le_add_left _ _
  have old := grid_to_compact t p H z S B a C E T both.andE₁ hH hp1
  have translated := grid_to_compact t p H (shifted z B) S B a C E T both.andE₂ hH hp1
  have fraction := GaussianGammaEulerHead.fraction_disk z R B h.andE₁.andE₁ h.andE₁.andE₂.andE₂
  have scaled : Γ ⊢[PRAAx] distanceBounded
      (qmul (ofGaussian z B) (ap2 compactF t (compactData z R B a C E T))) (qmul (ofGaussian z B) Q) R (unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance _ _ _ R one (unit t) (unit_positive t) fraction
        (distance_symmetric _ _ _ _ (unit_positive t) old))
  have grids : Γ ⊢[PRAAx] distanceBounded (rawLeft t z R B a C E T)
      (GaussianEulerIntegrationByPartsNormalizedGrid.normalized p N z B a C E) (R+one) (unit t) :=
    GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive t) scaled
      (distance_symmetric _ _ _ _ (unit_positive t) translated)
  have finite := GaussianEulerIntegrationByPartsCompact.original_compact_IBP t p N z S B a C E T (.andI both.andE₁ hC) hm hp0
  have ends := boundary_query_error p t z R B a C E T h hpt
  have first := left_readback t z R B a C E T h
  have last := distance_symmetric _ _ _ _ (unit_positive t) (boundary_readback t z R B a C E T h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive t) first
      (distance_triangle_same _ _ _ _ _ _ (unit_positive t) grids
        (distance_triangle_same _ _ _ _ _ _ (unit_positive t) finite
          (distance_triangle_same _ _ _ _ _ _ (unit_positive t) ends last))))

theorem positive_identity (z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    crossEquivalent leftF boundaryF (leftData z R B a C E T) (boundaryData z B a C E) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (gain z R B a C E T)
    (left_regular z R B a C E T h) (boundary_regular z R B a C E T h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift C) := by simpa [Fm.shift,Syn.shift] using hC.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_gain,subst_leftData,subst_boundaryData,Syn.shift] using
    positive_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs cs

theorem actual_original_positive_width_compact_IBP_name_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏ le one (var 4)) ⟶
      crossEquivalent leftF boundaryF (leftData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (boundaryData (var 0) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 7 (.impI (positive_identity _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

private theorem endpoint_zero_width (t z B a E : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerIntegrationByPartsCompact.boundary t z B a zero E ≐ qzero := by
  have e : Γ ⊢[PRAAx] GaussianEulerIntegrandName.sample t (shifted z B) B (a+zero) E ≐
      GaussianEulerIntegrandName.sample t (shifted z B) B a E := by
    ipra_congr (GaussianEulerIntegrandName.sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
      [.eqRefl t, .eqRefl (shifted z B), .eqRefl B, add_zero a, .eqRefl E]
  exact (GaussianRationalSyntheticDivision.qsub_congr e (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem zero_diagonal (t z R B a E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a zero E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 leftF t (leftData z R B a zero E T)) (ap2 boundaryF t (boundaryData z B a zero E))
      (productModulus z R B a zero E T+num 13) (unit t) := by
  have he := h.andE₁.andE₂.andE₁
  have original : Γ ⊢[PRAAx] ap2 compactF t (compactData z R B a zero E T) ≐ qzero :=
    GaussianCompactZeroWidth.observation_zero GaussianEulerIntegrandName.evaluatorF t a E (GaussianEulerCompactModulus.lipschitz (R+one) E T) T _ he
  have translated : Γ ⊢[PRAAx] ap2 compactF t (compactData (shifted z B) R B a zero E T) ≐ qzero :=
    GaussianCompactZeroWidth.observation_zero GaussianEulerIntegrandName.evaluatorF t a E (GaussianEulerCompactModulus.lipschitz (R+one) E T) T _ he
  have raw : Γ ⊢[PRAAx] rawLeft t z R B a zero E T ≐ qzero :=
    (GaussianRationalSyntheticDivision.qsub_congr
      ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) original).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)) translated).eqTrans
      (GaussianCoefficientNormOrder.qsub_self qzero)
  have left := distance_congr (.eqRefl _) raw (.eqRefl _) (.eqRefl _) (left_readback t z R B a zero E T h)
  have right := distance_congr (.eqRefl _) (endpoint_zero_width t z B a E) (.eqRefl _) (.eqRefl _) (boundary_readback t z R B a zero E T h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive t) left (distance_symmetric _ _ _ _ (unit_positive t) right))

theorem zero_identity (z R B a E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a zero E T) : Γ ⊢[PRAAx]
    crossEquivalent leftF boundaryF (leftData z R B a zero E T) (boundaryData z B a zero E) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (productModulus z R B a zero E T+num 13)
    (left_regular z R B a zero E T h) (boundary_regular z R B a zero E T h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] intervalSource (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) zero
      (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_leftData,subst_boundaryData,subst_productModulus,
    PTm.subst_add,ConciseIPRA.PTm.subst_zero,LeanProofs.IPRA.PTm.subst_num,Syn.shift] using
    zero_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift E) (Syn.shift T) hs

private def statement (z R B a C E T : PTm n) : Fm PTm n := intervalSource z R B a C E T ⟶
  crossEquivalent leftF boundaryF (leftData z R B a C E T) (boundaryData z B a C E)
@[simp] private theorem subst_statement {m : ℕ} (σ : Fin n → PTm m) (z R B a C E T : PTm n) :
    (statement z R B a C E T).subst σ = statement (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [statement]

private theorem statement_width_congr (z R B a C D E T : PTm n) (h : Γ ⊢[PRAAx] C ≐ D)
    (hc : Γ ⊢[PRAAx] statement z R B a C E T) : Γ ⊢[PRAAx] statement z R B a D E T := by
  simpa using
    Prf.eqSubst (Γ := Γ) (Ax := PRAAx) (statement (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : Fm PTm 7)
      ![z,R,B,a,C,E,T] ![z,R,B,a,D,E,T]
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact h; exact .eqRefl _; exact .eqRefl _)
      (by simpa using hc)

/-- All finite positive-time intervals, including width zero. The
boundary terms are actual original shifted endpoint PR2 names. -/
theorem original_compact_IBP_names (z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    crossEquivalent leftF boundaryF (leftData z R B a C E T) (boundaryData z B a C E) := by
  refine .orE (zero_or_succ C) ?_ ?_
  · have base : (C ≐ zero)::Γ ⊢[PRAAx] statement z R B a zero E T :=
      .impI (zero_identity z R B a E T Prf.hyp0)
    exact (statement_width_congr z R B a zero C E T Prf.hyp0.eqSymm base).impE h.wk
  · have positive : (C ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred C))::Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact positive_identity z R B a C E T h.wk positive

theorem actual_original_compact_Euler_IBP_regular_names_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (intervalSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      crossEquivalent leftF boundaryF (leftData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (boundaryData (var 0) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 7 (.impI (original_compact_IBP_names _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_compact_Euler_IBP_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (intervalSource (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      distanceBounded (ap2 leftF (var 0) (leftData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (ap2 boundaryF (var 1) (boundaryData (var 2) (var 4) (var 5) (var 6) (var 7)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 9 (.impI (cross_at _ _ _ _ _ _ (original_compact_IBP_names _ _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNamedIdentity
