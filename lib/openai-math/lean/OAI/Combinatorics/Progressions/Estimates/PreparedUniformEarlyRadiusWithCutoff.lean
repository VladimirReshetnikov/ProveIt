import OAI.Combinatorics.Progressions.Dynamics.AllocatedUnitSiteEarlyBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope
import OAI.Combinatorics.Progressions.Geometry.AllocatedProductChartRadius

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedBufferedRadiusInput {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  allocatedComparisonDimension m p + g + ((2 * m + 5) * (m + 1) + 5 : ℕ)

noncomputable def allocatedBufferedRadiusLog {A : Type*} [Semiring A] (m : ℕ) (p g : A) : A :=
  (m + 10 : ℕ) * (allocatedBufferedRadiusInput m p g + (m + 3 : ℕ))

noncomputable def allocatedCommonRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedBufferedRadiusLog m p g + allocatedIdealCoverPrimitiveLog m p g

noncomputable def allocatedCommonRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonRadiusLog m p g)

theorem allocatedBufferedRadiusInput_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    let P := allocatedBufferedRadiusInput m p g
    0 ≤ P ∧ allocatedComparisonDimension m p ≤ P ∧ g ≤ P ∧
      (((2 * m + 5) * (m + 1) + 5 : ℕ) : ℝ) ≤ P := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  dsimp only [allocatedBufferedRadiusInput]
  have ha : (0 : ℝ) ≤ ((2 * m + 5) * (m + 1) + 5 : ℕ) := Nat.cast_nonneg _
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem allocatedCommonRadiusLog_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonRadiusLog m p g ∧
      allocatedBufferedRadiusLog m p g ≤ allocatedCommonRadiusLog m p g ∧
      allocatedIdealCoverPrimitiveLog m p g ≤ allocatedCommonRadiusLog m p g := by
  have hP := (allocatedBufferedRadiusInput_bounds m hp hg).1
  have hb : 0 ≤ allocatedBufferedRadiusLog m p g := by
    unfold allocatedBufferedRadiusLog
    positivity
  have hi := (allocatedIdealCoverPrimitiveRadius_bounds m hp hg).1
  dsimp only [allocatedCommonRadiusLog]
  exact ⟨add_nonneg hb hi, le_add_of_nonneg_right hi, le_add_of_nonneg_left hb⟩

theorem allocatedCommonRadius_bounds (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 < allocatedCommonRadius m p g ∧ allocatedCommonRadius m p g ≤ 1 ∧
      (allocatedCommonRadius m p g)⁻¹ = Real.exp (allocatedCommonRadiusLog m p g) := by
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (allocatedCommonRadiusLog_bounds m hp hg).1)
  · simp only [allocatedCommonRadius, Real.exp_neg, inv_inv]

theorem allocatedCommonRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (_hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonRadiusLog m p g ≤ allocatedCommonRadiusLog m p' g' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  unfold allocatedCommonRadiusLog allocatedBufferedRadiusLog allocatedBufferedRadiusInput
    allocatedIdealCoverPrimitiveLog allocatedIdealCoverInputLog allocatedSiteCoefficientLog
  gcongr

theorem exists_allocatedCommonRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p g : ℝ, 0 ≤ p → 0 ≤ g →
      allocatedCommonRadiusLog m p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonRadiusLog_mono m hp hg
    (le_add_of_nonneg_right hg) (le_add_of_nonneg_left hp)).trans
  simpa [poly, allocatedCommonRadiusLog, allocatedBufferedRadiusLog, allocatedBufferedRadiusInput,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound (p + g) (add_nonneg hp hg)

section Charts

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedBufferedRadius_inverse_from_primitive {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (allocatedBufferedRadiusLog m p g) := by
  have hd := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun _ => Finset α) B
    (fun _ => id) hq (fun _ => Function.injective_id) hp hvars hI hn
  obtain ⟨hP, hDP, hgP, haP⟩ := allocatedBufferedRadiusInput_bounds m hp hg
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hqreal : (Fintype.card α : ℝ) ≤ (m + 1 : ℕ) := Nat.cast_le.mpr hq
  have hPe : allocatedBufferedRadiusInput m p g ≤ Real.exp (allocatedBufferedRadiusInput m p g) := by
    linarith [Real.add_one_le_exp (allocatedBufferedRadiusInput m p g)]
  have hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤
      allocatedBufferedRadiusInput m p g := by
    have hmul := mul_le_mul_of_nonneg_left hqreal
      (show (0 : ℝ) ≤ (2 * m + 5 : ℕ) by positivity)
    push_cast at haP hmul ⊢
    linarith
  have hi := allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform B α C hC hP
    (hd.degree.trans (hDP.trans hPe)) (hd.cube.trans hDP) hallow
    (fun j => (hCg j).trans (Real.exp_le_exp.mpr hgP))
    (fun j => (hd.coefficients j).trans (hDP.trans hPe))
    (fun j => (hI j).trans (hpD.trans (hDP.trans hPe))) j
  apply hi.trans
  apply Real.exp_le_exp.mpr
  unfold allocatedBufferedRadiusLog
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  push_cast at hqreal
  linarith

theorem allocatedCommonRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j := by
  obtain ⟨_, hb, hi⟩ := allocatedCommonRadiusLog_bounds m hp hg
  have hbuffer : allocatedCommonRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
    have hinv := (allocatedBufferedRadius_inverse_from_primitive B hp hg hq hvars hI hn C hC hCg j).trans
      (Real.exp_le_exp.mpr hb)
    have hpos := allocatedBufferedPhysicalChartRadius_pos (G := G) B α C hC j
    have h := (inv_le_inv₀ (Real.exp_pos (allocatedCommonRadiusLog m p g)) (inv_pos.mpr hpos)).2 hinv
    simpa only [allocatedCommonRadius, Real.exp_neg, inv_inv] using h
  refine ⟨hbuffer, hbuffer.trans (allocatedBufferedPhysicalChartRadius_le_original B α C hC j), ?_⟩
  apply le_trans _ (allocatedIdealCoverPrimitiveRadius_le B rowSets hp hg hq hvars hI hn C hC hCg j)
  exact Real.exp_le_exp.mpr (neg_le_neg hi)

end Charts

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonProductRadiusLog {A : Type*} [Semiring A]
    (m : ℕ) (p g : A) : A :=
  allocatedCommonRadiusLog m p g +
    allocatedProductChartLog m (allocatedComparisonDimension m p) g

noncomputable def allocatedCommonProductRadius (m : ℕ) (p g : ℝ) : ℝ :=
  Real.exp (-allocatedCommonProductRadiusLog m p g)

theorem allocatedCommonProductRadius_bounds (m : ℕ) {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonProductRadiusLog m p g ∧
      0 < allocatedCommonProductRadius m p g ∧ allocatedCommonProductRadius m p g ≤ 1 ∧
      (allocatedCommonProductRadius m p g)⁻¹ = Real.exp (allocatedCommonProductRadiusLog m p g) ∧
      allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g ∧
      allocatedCommonProductRadius m p g ≤
        allocatedProductChartRadius m (allocatedComparisonDimension m p) g ∧
      allocatedCommonProductRadius m p g ≤ allocatedSourceCoverRadius m p g := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hcommon := (allocatedCommonRadiusLog_bounds m hp hg).1
  have hproduct := (allocatedProductChartLog_bounds m hD hg).2.2.2.2.2.2
  have hlog : 0 ≤ allocatedCommonProductRadiusLog m p g := add_nonneg hcommon hproduct
  have hc : allocatedCommonProductRadius m p g ≤ allocatedCommonRadius m p g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right hproduct))
  have hp' : allocatedCommonProductRadius m p g ≤
      allocatedProductChartRadius m (allocatedComparisonDimension m p) g :=
    Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_left hcommon))
  refine ⟨hlog, Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog), ?_, hc, hp', ?_⟩
  · simp only [allocatedCommonProductRadius, Real.exp_neg, inv_inv]
  · exact hp'.trans (allocatedProductChartRadius_bounds m hD hg).2.2.2

theorem allocatedCommonProductRadiusLog_mono (m : ℕ) {p g p' g' : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hpp : p ≤ p') (hgg : g ≤ g') :
    allocatedCommonProductRadiusLog m p g ≤ allocatedCommonProductRadiusLog m p' g' := by
  exact add_le_add (allocatedCommonRadiusLog_mono m hp hg hpp hgg)
    (allocatedProductChartLog_mono m (allocatedComparisonDimension_bounds m hp).1
      (allocatedComparisonDimension_mono m hp hpp) hgg)

theorem exists_allocatedCommonProductRadiusLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      allocatedCommonProductRadiusLog m p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ := allocatedCommonProductRadiusLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonProductRadiusLog_mono m hp hg (le_add_of_nonneg_right hg)
    (le_add_of_nonneg_left hp)).trans
  simpa [poly, allocatedCommonProductRadiusLog, allocatedCommonRadiusLog,
    allocatedBufferedRadiusLog, allocatedBufferedRadiusInput, allocatedProductChartLog,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hb (p + g) (add_nonneg hp hg)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedCommonProductRadius_admissible {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonProductRadius m p g ≤ allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonProductRadius m p g ≤ allocatedIdealCoverRadius (G := G) B rowSets C j ∧
      allocatedCommonProductRadius m p g ≤ allocatedProductGridRadius (G := G) B rowSets C j := by
  obtain ⟨_, _, _, _, hcommon, hproduct, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  obtain ⟨hbuffer, hphysical, hideal⟩ := allocatedCommonRadius_admissible B rowSets
    hp hg hq hvars hI hn C hC hCg j
  have hdim := allocatedComparisonDimensions_of_primitive (G := G) (α := α)
    (O := fun k => (rowSets k : Type _)) B (fun k => (Subtype.val : rowSets k → Finset α))
    hq (fun _ => Subtype.val_injective) hp hvars hI hn
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hgrid := (allocatedProductChartRadius_le_charts B rowSets hdim hg
    (fun k => (hI k).trans hpD) (fun k => (hn k).trans hpD) C hC hCg j).1
  exact ⟨hcommon.trans hbuffer, hcommon.trans hphysical, hcommon.trans hideal, hproduct.trans hgrid⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

theorem allocatedCanonicalSlice_source_geometry
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedCommonProductRadius m p g) :
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  intro T r
  have hgrid (j) : R j ≤ allocatedProductGridRadius (G := G) B rowSets C j :=
    (hsmall j).trans (allocatedCommonProductRadius_admissible B rowSets hp hg hdim hvars hI hn C hC hCg j).2.2.2
  have hT0 := allocatedIdealCoverSupport_nonneg (G := G) B rowSets
  have hrdom := allocatedProductIdealSiteRadius_dominates (G := G) B rowSets
  refine ⟨allocatedProductIdealSiteRadius_one_le B rowSets, hT0,
    allocatedIdealCoverSupport_ideal B rowSets, allocatedIdealCoverSupport_inactive B rowSets,
    hrdom, ?_, allocatedProductGridRadius_recovery_budget B rowSets C hC hR hgrid⟩
  intro j
  have hrow : (1 : ℝ) ≤ (rowSets j).card := by
    let a : rowSets j := Classical.choice (inferInstance : Nonempty (rowSets j))
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a.val, a.property⟩)
  have hTr : T j ≤ (r : ℝ) := by
    calc
      _ ≤ (rowSets j).card * T j := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow (hT0 j)
      _ ≤ _ := hrdom j
  have hT2r : T j ≤ 2 * (r : ℝ) := by linarith [r.coe_nonneg]
  apply le_trans _ (allocatedProductGridRadius_source_budget B rowSets C hC hR hgrid j)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2r (hR j)) (by positivity)) (hC j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped Classical

attribute [local instance 2000] fullBooleanRowSetFintype

theorem allocatedComparisonDimension_two_mul (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    2 * p ≤ allocatedComparisonDimension m p := by
  have h := (allocatedComparisonDimension_bounds m hp).2.2.2.2.2.1
  have hm : (2 : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show 2 ≤ m + 2 by omega)
  exact (mul_le_mul_of_nonneg_right hm hp).trans h

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

include hb bW in
theorem allocatedCanonicalSourceGeometry
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ 2 * p) :
    let D := allocatedComparisonDimension m p
    AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j => (rowSets j : Type _)) D ∧
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ D ∧
      (∀ j, (Fintype.card (I j) : ℝ) ≤ D) ∧ (∀ j, (n j : ℝ) ≤ D) ∧
      (∀ j, (Fintype.card (Kcov j) : ℝ) ≤ D) ∧
      allocatedCommonProductRadius m p g ≤ allocatedProductChartRadius m D g := by
  have hpD := (allocatedComparisonDimension_bounds m hp).2.2.1
  refine ⟨allocatedComparisonDimensions_of_primitive B
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective)
    hp hvars hI hn, hvars.trans hpD, fun j => (hI j).trans hpD,
    fun j => (hn j).trans hpD, ?_, (allocatedCommonProductRadius_bounds m hp hg).2.2.2.2.2.1⟩
  intro j
  exact (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans
    ((hJ j).trans (allocatedComparisonDimension_two_mul m hp))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCommonProductRadiusLogWithCutoff {A : Type*} [Semiring A]
    (m d : ℕ) (p g : A) : A :=
  allocatedCommonProductRadiusLog (max m d) (p + (d + 1 : ℕ)) g

noncomputable def allocatedCommonProductRadiusWithCutoff (m d : ℕ) (p g : ℝ) : ℝ :=
  allocatedCommonProductRadius (max m d) (p + (d + 1 : ℕ)) g

theorem allocatedCommonProductRadiusWithCutoff_bounds (m d : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) :
    0 ≤ allocatedCommonProductRadiusLogWithCutoff m d p g ∧
      0 < allocatedCommonProductRadiusWithCutoff m d p g ∧
      allocatedCommonProductRadiusWithCutoff m d p g ≤ 1 ∧
      (allocatedCommonProductRadiusWithCutoff m d p g)⁻¹ =
        Real.exp (allocatedCommonProductRadiusLogWithCutoff m d p g) := by
  obtain ⟨hlog, hpos, hone, hinv, _⟩ :=
    allocatedCommonProductRadius_bounds (max m d)
      (show 0 ≤ p + (d + 1 : ℕ) by positivity) hg
  exact ⟨hlog, hpos, hone, hinv⟩

theorem exists_allocatedCommonProductRadiusLogWithCutoff_bound (m d : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      allocatedCommonProductRadiusLogWithCutoff m d p g ≤ (p + g + a) ^ a := by
  let poly : Polynomial ℕ :=
    allocatedCommonProductRadiusLogWithCutoff m d Polynomial.X Polynomial.X
  obtain ⟨a, ha, hb⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p g hp hg
  apply (allocatedCommonProductRadiusLog_mono (max m d)
    (show 0 ≤ p + (d + 1 : ℕ) by positivity) hg
    (show p + (d + 1 : ℕ) ≤ p + g + (d + 1 : ℕ) by linarith)
    (show g ≤ p + g by linarith)).trans
  simpa [poly, allocatedCommonProductRadiusLogWithCutoff, allocatedCommonProductRadiusLog,
    allocatedCommonRadiusLog, allocatedBufferedRadiusLog, allocatedBufferedRadiusInput,
    allocatedProductChartLog, allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog,
    allocatedSiteCoefficientLog, allocatedComparisonDimension, Polynomial.eval₂_pow]
    using hb (p + g) (add_nonneg hp hg)

theorem allocatedProductChartLog_mono_layers {m M : ℕ} (hm : m ≤ M) {D c : ℝ}
    (hD : 0 ≤ D) :
    allocatedProductChartLog m D c ≤ allocatedProductChartLog M D c := by
  unfold allocatedProductChartLog allocatedIdealCoverInputLog
  gcongr

section Charts

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedBufferedRadius_inverse_from_primitive_with_cutoff (d : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ d + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    (allocatedBufferedPhysicalChartRadius (G := G) B α C j)⁻¹ ≤
      Real.exp (allocatedBufferedRadiusLog (max m d) (p + (d + 1 : ℕ)) g) := by
  let M := max m d
  let p' := p + (d + 1 : ℕ)
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp' : p ≤ p' := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hd := allocatedComparisonDimensions_of_primitive_with_cutoff (G := G) (α := α)
    (O := fun _ => Finset α) B d (fun _ => id) hq (fun _ => Function.injective_id)
    hp hvars hI hn
  obtain ⟨hP, hDP, hgP, haP⟩ := allocatedBufferedRadiusInput_bounds M hp' hg
  have hpD := (allocatedComparisonDimension_bounds M hp').2.2.1
  have hqM : Fintype.card α ≤ M + 1 := hq.trans (Nat.add_le_add_right (Nat.le_max_right m d) 1)
  have hqreal : (Fintype.card α : ℝ) ≤ (M + 1 : ℕ) := Nat.cast_le.mpr hqM
  have hmreal : (m : ℝ) ≤ M := Nat.cast_le.mpr (Nat.le_max_left m d)
  have hPe : allocatedBufferedRadiusInput M p' g ≤
      Real.exp (allocatedBufferedRadiusInput M p' g) := by
    linarith [Real.add_one_le_exp (allocatedBufferedRadiusInput M p' g)]
  have hallow : ((2 * m : ℕ) + 5) * (Fintype.card α : ℝ) + 5 ≤
      allocatedBufferedRadiusInput M p' g := by
    have hmul : (((2 * m : ℕ) + 5) : ℝ) * (Fintype.card α : ℝ) ≤
        ((2 * M + 5 : ℕ) : ℝ) * (M + 1 : ℕ) := by
      apply mul_le_mul _ hqreal (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      push_cast
      linarith
    push_cast at haP hmul ⊢
    linarith
  have hi := allocatedBufferedPhysicalChartRadius_inv_le_exp_uniform B α C hC hP
    (hd.degree.trans (hDP.trans hPe)) (hd.cube.trans hDP) hallow
    (fun j => (hCg j).trans (Real.exp_le_exp.mpr hgP))
    (fun j => (hd.coefficients j).trans (hDP.trans hPe))
    (fun j => (hI j).trans (hpp'.trans (hpD.trans (hDP.trans hPe)))) j
  apply hi.trans
  apply Real.exp_le_exp.mpr
  change ((m : ℝ) + 10) * (allocatedBufferedRadiusInput M p' g +
    (Fintype.card α : ℝ) + 2) ≤
    ((M + 10 : ℕ) : ℝ) * (allocatedBufferedRadiusInput M p' g + (M + 3 : ℕ))
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hqreal ⊢
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

theorem allocatedCommonProductRadiusWithCutoff_admissible (d : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hq : Fintype.card α ≤ d + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g) (j : Fin m) :
    allocatedCommonProductRadiusWithCutoff m d p g ≤
        allocatedBufferedPhysicalChartRadius (G := G) B α C j ∧
      allocatedCommonProductRadiusWithCutoff m d p g ≤
        allocatedPhysicalChartRadius (G := G) B α C 1 j ∧
      allocatedCommonProductRadiusWithCutoff m d p g ≤
        allocatedIdealCoverRadius (G := G) B rowSets C j ∧
      allocatedCommonProductRadiusWithCutoff m d p g ≤
        allocatedProductGridRadius (G := G) B rowSets C j := by
  let M := max m d
  let p' := p + (d + 1 : ℕ)
  have hp' : 0 ≤ p' := by dsimp [p']; positivity
  have hpp' : p ≤ p' := le_add_of_nonneg_right (Nat.cast_nonneg _)
  obtain ⟨_, _, _, _, hcommon, hproduct, _⟩ := allocatedCommonProductRadius_bounds M hp' hg
  have hb := (allocatedCommonRadiusLog_bounds M hp' hg).2.1
  have hbuffer : allocatedCommonProductRadiusWithCutoff m d p g ≤
      allocatedBufferedPhysicalChartRadius (G := G) B α C j := by
    have hinv := (allocatedBufferedRadius_inverse_from_primitive_with_cutoff B d
      hp hg hq hvars hI hn C hC hCg j).trans (Real.exp_le_exp.mpr hb)
    have hpos := allocatedBufferedPhysicalChartRadius_pos (G := G) B α C hC j
    have h := (inv_le_inv₀ (Real.exp_pos (allocatedCommonRadiusLog M p' g))
      (inv_pos.mpr hpos)).2 hinv
    apply hcommon.trans
    simpa only [allocatedCommonRadius, Real.exp_neg, inv_inv] using h
  have hdim := allocatedComparisonDimensions_of_primitive_with_cutoff (G := G) (α := α)
    (O := fun k => (rowSets k : Type _)) B d
    (fun k => (Subtype.val : rowSets k → Finset α)) hq
    (fun _ => Subtype.val_injective) hp hvars hI hn
  have hD := (allocatedComparisonDimension_bounds M hp').1
  have hpD := (allocatedComparisonDimension_bounds M hp').2.2.1
  have hproduct' : allocatedCommonProductRadiusWithCutoff m d p g ≤
      allocatedProductChartRadius m (allocatedComparisonDimension M p') g := by
    apply hproduct.trans
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (allocatedProductChartLog_mono_layers (Nat.le_max_left m d) hD)
  obtain ⟨hgrid, hphysical, hideal⟩ := allocatedProductChartRadius_le_charts B rowSets hdim hg
    (fun k => (hI k).trans (hpp'.trans hpD))
    (fun k => (hn k).trans (hpp'.trans hpD)) C hC hCg j
  exact ⟨hbuffer, hproduct'.trans hphysical, hproduct'.trans hideal, hproduct'.trans hgrid⟩

end Charts
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem allocatedCommonProductRadiusLog_ge_geometry (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) : g ≤ allocatedCommonProductRadiusLog m p g := by
  have hinput := allocatedBufferedRadiusInput_bounds m hp hg
  have hcommon := allocatedCommonRadiusLog_bounds m hp hg
  have hproduct := (allocatedProductChartLog_bounds m (allocatedComparisonDimension_bounds m hp).1 hg).2.2.2.2.2.2
  calc
    g ≤ allocatedBufferedRadiusInput m p g := hinput.2.2.1
    _ ≤ allocatedBufferedRadiusLog m p g := by
      unfold allocatedBufferedRadiusLog
      have hm : (1 : ℝ) ≤ (m + 10 : ℕ) := by exact_mod_cast (show 1 ≤ m + 10 by omega)
      calc
        _ ≤ allocatedBufferedRadiusInput m p g + (m + 3 : ℕ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
        _ ≤ _ := le_mul_of_one_le_left (add_nonneg hinput.1 (Nat.cast_nonneg _)) hm
    _ ≤ allocatedCommonRadiusLog m p g := hcommon.2.1
    _ ≤ allocatedCommonProductRadiusLog m p g := le_add_of_nonneg_right hproduct

theorem allocatedCommonProductRadius_le_exp_neg_geometry (m : ℕ) {p g : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) : allocatedCommonProductRadius m p g ≤ Real.exp (-g) :=
  Real.exp_le_exp.mpr (neg_le_neg (allocatedCommonProductRadiusLog_ge_geometry m hp hg))

theorem allocatedCommonProductRadius_freezing_sum (m : ℕ) (dim rank : Fin m → ℕ)
    {p c q : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hm : (m : ℝ) ≤ p) (hdim : ∀ j, (dim j : ℝ) ≤ p) (hrank : ∀ j, (rank j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCc : ∀ j, C j ≤ Real.exp c) :
    (∑ j, (dim j : ℝ) * (C j * (((rank j : ℝ) + 1) *
      allocatedCommonProductRadius m p (3 * p + c + q)))) ≤ Real.exp (-q) := by
  let R := allocatedCommonProductRadius m p (3 * p + c + q)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hRupper : R ≤ Real.exp (-(3 * p + c + q)) :=
    allocatedCommonProductRadius_le_exp_neg_geometry m hp (by positivity)
  have hpExp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hterm (j : Fin m) : (dim j : ℝ) * (C j * (((rank j : ℝ) + 1) * R)) ≤
      Real.exp p * (Real.exp c * (Real.exp p * R)) := by
    apply mul_le_mul ((hdim j).trans hpExp)
    · apply mul_le_mul (hCc j)
      · exact mul_le_mul_of_nonneg_right (by linarith [hrank j, Real.add_one_le_exp p]) hR
      · positivity
      · positivity
    · exact mul_nonneg (hC j) (mul_nonneg (by positivity) hR)
    · positivity
  calc
    _ ≤ ∑ _j : Fin m, Real.exp p * (Real.exp c * (Real.exp p * R)) :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = (m : ℝ) * (Real.exp p * (Real.exp c * (Real.exp p * R))) := by simp
    _ ≤ Real.exp p * (Real.exp p * (Real.exp c * (Real.exp p * Real.exp (-(3 * p + c + q))))) := by
      apply mul_le_mul (hm.trans hpExp)
      · gcongr
      · positivity
      · positivity
    _ = Real.exp (-q) := by simp only [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedFiniteForwardTailCap_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (x : ℝ) (a n : Fin m → ℕ) (V : Fin m → ℝ),
      0 ≤ x → (m : ℝ) ≤ x →
      (∀ j, (a j : ℝ) ≤ x) → (∀ j, (n j : ℝ) ≤ x) →
      (∀ j, 0 ≤ V j) → (∀ j, V j ≤ Real.exp x) →
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp x →
      4 * (∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m x x) (V j)) ≤ Real.exp ((x + C) ^ C) := by
  obtain ⟨Ar, hAr, hradius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let P : Polynomial ℕ := Polynomial.X + (2 * Polynomial.X + Polynomial.C Ar) ^ Ar + 1
  let Q : Polynomial ℕ := 3 * P ^ 3 + 17 * P ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x a n V hx hm ha hn hV hVx hLipschitz
  let p : ℝ := x + (2 * x + Ar) ^ Ar + 1
  have hp0 : 0 ≤ p := by dsimp only [p]; positivity
  have hxp : x ≤ p := by
    have hpow : 0 ≤ (2 * x + Ar) ^ Ar := by positivity
    dsimp only [p]
    linarith only [hpow]
  have hlog : allocatedCommonProductRadiusLog m x x ≤ p := by
    have h : allocatedCommonProductRadiusLog m x x ≤ (2 * x + Ar) ^ Ar := by
      simpa only [two_mul] using hradius hx hx
    dsimp only [p]
    linarith only [h, hx]
  have hb := allocatedCommonProductRadius_bounds m hx hx
  have hexp : Real.exp x ≤ Real.exp p := Real.exp_le_exp.mpr hxp
  have htail := earlyFiberCap_exp_bound a n
    (fun _ => allocatedCommonProductRadius m x x) V hp0 (hm.trans hxp)
    (fun _ => hb.2.1) hV (fun j => (ha j).trans hxp) (fun j => (hn j).trans hxp)
    (hLipschitz.trans hexp)
    (fun _ => hb.2.2.2.1.le.trans (Real.exp_le_exp.mpr hlog))
    (fun j => (hVx j).trans hexp)
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by
    linarith only [Real.add_one_le_exp (4 : ℝ)]
  have hpoly : earlyFiberCapLog p + 4 ≤ (x + C) ^ C := by
    simpa [Q, P, p, earlyFiberCapLog, Polynomial.eval₂_pow] using hbudget x hx
  calc
    4 * (∏ j, earlyConstantDensityCap (a j) (n j)
        (allocatedCommonProductRadius m x x) (V j))
      ≤ 4 * Real.exp (earlyFiberCapLog p) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ ≤ Real.exp 4 * Real.exp (earlyFiberCapLog p) :=
      mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = Real.exp (earlyFiberCapLog p + 4) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp ((x + C) ^ C) := Real.exp_le_exp.mpr hpoly

noncomputable def preparedFiniteForwardTailCapExponent (m : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardTailCap_budget m)

theorem preparedFiniteForwardTailCapExponent_two_le (m : ℕ) :
    2 ≤ preparedFiniteForwardTailCapExponent m :=
  (Classical.choose_spec (exists_preparedFiniteForwardTailCap_budget m)).1

theorem preparedFiniteForwardTailCap_le_exp (m : ℕ)
    (x : ℝ) (a n : Fin m → ℕ) (V : Fin m → ℝ)
    (hx : 0 ≤ x) (hm : (m : ℝ) ≤ x)
    (ha : ∀ j, (a j : ℝ) ≤ x) (hn : ∀ j, (n j : ℝ) ≤ x)
    (hV : ∀ j, 0 ≤ V j) (hVx : ∀ j, V j ≤ Real.exp x)
    (hLipschitz : (probabilityProfileLipschitz : ℝ) ≤ Real.exp x) :
    4 * (∏ j, earlyConstantDensityCap (a j) (n j)
      (allocatedCommonProductRadius m x x) (V j)) ≤
      Real.exp ((x + preparedFiniteForwardTailCapExponent m) ^
        preparedFiniteForwardTailCapExponent m) :=
  (Classical.choose_spec (exists_preparedFiniteForwardTailCap_budget m)).2
    x a n V hx hm ha hn hV hVx hLipschitz

theorem preparedFiniteForward_shiftedPower_le_work (A C : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage : ℕ) {x : ℝ}
    (hA : 2 ≤ A) (hC : C ≤ A) (hx : 0 ≤ x) :
    (x + C) ^ C ≤ preparedFiniteForwardWork A stageCountConstant stage x := by
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant stage hx
  have hxp := le_preparedFiniteForwardParameter A stageCountConstant stage hx
  have hAreal : (2 : ℝ) ≤ A := Nat.cast_le.mpr hA
  have hCreal : (C : ℝ) ≤ A := Nat.cast_le.mpr hC
  rw [preparedFiniteForwardWork_eq]
  exact (pow_le_pow_left₀ (add_nonneg hx (Nat.cast_nonneg C))
    (add_le_add hxp hCreal) C).trans
      (pow_le_pow_right₀ (by linarith only [hp, hAreal]) hC)

theorem preparedFiniteForwardTailCap_le_exp_work (m A : ℕ)
    (stageCountConstant : ℕ → ℕ) (stage : ℕ)
    (x : ℝ) (a n : Fin m → ℕ) (V : Fin m → ℝ)
    (hA : 2 ≤ A) (hC : preparedFiniteForwardTailCapExponent m ≤ A)
    (hx : 0 ≤ x) (hm : (m : ℝ) ≤ x)
    (ha : ∀ j, (a j : ℝ) ≤ x) (hn : ∀ j, (n j : ℝ) ≤ x)
    (hV : ∀ j, 0 ≤ V j) (hVx : ∀ j, V j ≤ Real.exp x)
    (hLipschitz : (probabilityProfileLipschitz : ℝ) ≤ Real.exp x) :
    4 * (∏ j, earlyConstantDensityCap (a j) (n j)
      (allocatedCommonProductRadius m x x) (V j)) ≤
      Real.exp (preparedFiniteForwardWork A stageCountConstant stage x) :=
  (preparedFiniteForwardTailCap_le_exp m x a n V hx hm ha hn hV hVx hLipschitz).trans
    (Real.exp_le_exp.mpr (preparedFiniteForward_shiftedPower_le_work A
      (preparedFiniteForwardTailCapExponent m) stageCountConstant stage hA hC hx))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable [∀ j, Nonempty (rowSets j)]

theorem allocatedCanonicalSlice_source_geometry_with_cutoff (d : ℕ)
    {p g : ℝ} (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ d + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCg : ∀ j, C j ≤ Real.exp g)
    {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedCommonProductRadiusWithCutoff m d p g) :
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
      (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
      (∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
      (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  intro T r
  have hgrid (j) : R j ≤ allocatedProductGridRadius (G := G) B rowSets C j :=
    (hsmall j).trans (allocatedCommonProductRadiusWithCutoff_admissible B rowSets d hp hg hdim hvars hI hn C hC hCg j).2.2.2
  have hT0 := allocatedIdealCoverSupport_nonneg (G := G) B rowSets
  have hrdom := allocatedProductIdealSiteRadius_dominates (G := G) B rowSets
  refine ⟨allocatedProductIdealSiteRadius_one_le B rowSets, hT0,
    allocatedIdealCoverSupport_ideal B rowSets, allocatedIdealCoverSupport_inactive B rowSets,
    hrdom, ?_, allocatedProductGridRadius_recovery_budget B rowSets C hC hR hgrid⟩
  intro j
  have hrow : (1 : ℝ) ≤ (rowSets j).card := by
    let a : rowSets j := Classical.choice (inferInstance : Nonempty (rowSets j))
    exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨a.val, a.property⟩)
  have hTr : T j ≤ (r : ℝ) := by
    calc
      _ ≤ (rowSets j).card * T j := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow (hT0 j)
      _ ≤ _ := hrdom j
  have hT2r : T j ≤ 2 * (r : ℝ) := by linarith [r.coe_nonneg]
  apply le_trans _ (allocatedProductGridRadius_source_budget B rowSets C hC hR hgrid j)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT2r (hR j)) (by positivity)) (hC j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformEarlyRadius_with_cutoff (m d : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      let pRadius := allocatedCommonProductRadiusLogWithCutoff m d p g
      let R : Fin m → ℝ := fun _ => allocatedCommonProductRadiusWithCutoff m d p g
      pRadius ∈ Set.Icc 0 ((p + g + A) ^ A) ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      ∀ {G : Type uG} [Fintype G] {I : Fin m → Type uI} [∀ j, Fintype (I j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {α : Type uα} [Fintype α] (rowSets : Fin m → Finset (Finset α))
        [∀ j, Nonempty (rowSets j)],
        Fintype.card α ≤ d + 1 →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        let T := allocatedIdealCoverSupport (G := G) B rowSets
        let r := allocatedProductIdealSiteRadius (G := G) B rowSets
        1 ≤ r ∧ (∀ j, 0 ≤ T j) ∧
        (∀ j, partitionedIdealRadius α m + 1 ≤ T j) ∧
        (∀ j, (Fintype.card (BoundedCoefficientExponent
          (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
          ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j) ∧
        (∀ j, (rowSets j).card * T j ≤ (r : ℝ)) ∧
        ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp g) →
          (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
          (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
          (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
            (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4) := by
  obtain ⟨A, hA, hbound⟩ := exists_allocatedCommonProductRadiusLogWithCutoff_bound m d
  refine ⟨A, hA, ?_⟩
  intro p g hp hg pRadius R
  obtain ⟨hlog, hpos, hone, hinv⟩ := allocatedCommonProductRadiusWithCutoff_bounds m d hp hg
  refine ⟨⟨hlog, hbound hp hg⟩, fun _ => ⟨hpos, hone, hinv.le⟩, ?_⟩
  intro G _ I _ n B _ α _ rowSets _ hdim hvars hI hn
  dsimp only
  have hgeo := allocatedCanonicalSlice_source_geometry_with_cutoff B rowSets d hp hg hdim hvars hI hn
    (fun _ => 0) (fun _ => le_refl 0) (fun _ => Real.exp_nonneg g)
    (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadiusWithCutoff m d p g))
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeo.2.2.2.1, hgeo.2.2.2.2.1, ?_⟩
  intro C hC hCg
  have hgeometry := allocatedCanonicalSlice_source_geometry_with_cutoff B rowSets d hp hg hdim hvars hI hn
    C hC hCg (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadiusWithCutoff m d p g))
  refine ⟨?_, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2⟩
  intro j
  have hT : 1 ≤ allocatedIdealCoverSupport (G := G) B rowSets j := by
    linarith [hgeometry.2.2.1 j, partitionedIdealRadius_nonneg α m]
  calc
    _ = C j * (((Fintype.card (I j) : ℝ) + 1) * (1 * R j)) := by ring
    _ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
        (allocatedIdealCoverSupport (G := G) B rowSets j * R j)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hpos.le) (by positivity)) (hC j)
    _ ≤ _ := hgeometry.2.2.2.2.2.1 j

end Erdos3.VectorPolynomial

end

end OAI
