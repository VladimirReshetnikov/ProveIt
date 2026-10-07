import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyAccuracy
import OAI.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog

namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def physicalIdealSmoothingLog (h : D → ℕ) (A T : ℝ≥0) (E W : ℝ) : ℝ :=
  2 * booleanRegularizationInputLog (B := B) (O := O) (α := α) h
    (unitProfileCoefficientLog (B := B) A T) (E + W + 4) + 2

noncomputable def physicalIdealTailLog (G Z : Type*) [Fintype G] [Fintype Z]
    (h : D → ℕ) (A T : ℝ≥0) (degree : ℕ) (E W : ℝ) : ℝ :=
  6 * booleanMassInputLog (B := B) (O := O) (α := α) h degree
    (unitProfileCoefficientLog (B := B) A T) (E + W + 4)
    (samplerParameterLog G Z α (B := B) h) + 8

theorem physicalIdealSmoothingLog_nonneg (h : D → ℕ) (A T : ℝ≥0)
    {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W) :
    0 ≤ physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T E W := by
  have hb := booleanRegularizationInputLog_nonneg (B := B) (O := O) (α := α) h
    (unitProfileCoefficientLog_nonneg (B := B) A T) (show 0 ≤ E + W + 4 by positivity)
  unfold physicalIdealSmoothingLog
  positivity

theorem physicalIdealTailLog_nonneg (G Z : Type*) [Fintype G] [Fintype Z]
    (h : D → ℕ) (A T : ℝ≥0) (degree : ℕ)
    {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W) :
    0 ≤ physicalIdealTailLog (B := B) (O := O) (α := α) G Z h A T degree E W := by
  have hb := booleanMassInputLog_nonneg (B := B) (O := O) (α := α) h degree
    (unitProfileCoefficientLog_nonneg (B := B) A T) (show 0 ≤ E + W + 4 by positivity)
    (samplerParameterLog_nonneg (B := B) G Z α h)
  unfold physicalIdealTailLog
  positivity

theorem physicalIdeal_smoothing_inverse_le_exp [DecidableEq α] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (A T : ℝ≥0)
    {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W) :
    (booleanRegularizationRadius (B := B) (O := O) (α := α) h
      (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
      A T (physicalIdealErrorShare E W / 2))⁻¹ ≤
      Real.exp (physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T E W) :=
  uniformProfileRadius_inverse_le_exp h hh A T
    (div_pos (physicalIdealErrorShare_pos E W) (by norm_num))
    (by positivity) (physicalIdealErrorShare_half_inverse_le E W)

theorem physicalIdeal_tail_inverse_le_exp [DecidableEq α] [∀ d, Nonempty (O d)]
    (G Z : Type*) [Fintype G] [Fintype Z]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (A T : ℝ≥0) (degree : ℕ)
    {E W : ℝ} (hE : 0 ≤ E) (hW : 0 ≤ W) :
    (booleanMassPerturbationScale (B := B) (O := O) (α := α)
      (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d)) h
      (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
      A T degree 1 (physicalIdealErrorShare E W / 2))⁻¹ ≤
      Real.exp (physicalIdealTailLog (B := B) (O := O) (α := α) G Z h A T degree E W) :=
  uniformProfileScale_inverse_le_exp G Z α h hh A T degree
    (div_pos (physicalIdealErrorShare_pos E W) (by norm_num))
    (by positivity) (physicalIdealErrorShare_half_inverse_le E W)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedErrorPrimitiveLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  let D := allocatedComparisonDimension m p
  D + D ^ 3 + (layerTailDegree m + 1 : ℕ) * p + D ^ 3 * ((m + 1 : ℕ) * p)

theorem allocatedErrorPrimitiveLog_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let D := allocatedComparisonDimension m p
    let T := allocatedErrorPrimitiveLog m p
    0 ≤ T ∧ p ≤ T ∧ D ≤ T ∧ D ^ 3 ≤ T ∧
      (layerTailDegree m + 1 : ℕ) * p ≤ T ∧ D ^ 3 * ((m + 1 : ℕ) * p) ≤ T := by
  obtain ⟨hD, _, hpD, _⟩ := allocatedComparisonDimension_bounds m hp
  have hD3 : 0 ≤ (allocatedComparisonDimension m p) ^ 3 := pow_nonneg hD _
  have hS : 0 ≤ ((layerTailDegree m + 1 : ℕ) : ℝ) * p := by positivity
  have hA : 0 ≤ (allocatedComparisonDimension m p) ^ 3 * ((m + 1 : ℕ) * p) := by positivity
  dsimp only [allocatedErrorPrimitiveLog]
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedErrorPrimitive_constants
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1))
    (η : ℝ≥0) (C V : Fin m → ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hη : η ≤ 1) (hM : (M : ℝ) ≤ Real.exp p) (hS : (S.value : ℝ) ≤ Real.exp p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    let T := allocatedErrorPrimitiveLog m p
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period)
    (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ T ∧
      (allocatedErrorKernelCap B U b S (O := O) η A V : ℝ) ≤ Real.exp (allocatedErrorKernelLog T) ∧
      (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp (allocatedErrorKernelLog T) := by
  let D := allocatedComparisonDimension m p
  let T := allocatedErrorPrimitiveLog m p
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  obtain ⟨hT, hpT, hDT, hD3T, hST, hAT⟩ := allocatedErrorPrimitiveLog_bounds m hp
  have hpD : p ≤ D := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hQD (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans ((hJ j).trans hpD)
  have hper : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
      _ ≤ Real.exp p ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul p (m + 1)).symm
  have hA : (Real.toNNReal (coefficientDeckPeriodCap O Q period) : ℝ) ≤ Real.exp T := by
    rw [Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
    exact (coefficientDeckPeriodCap_exp_bound O Q period hd.nonneg (by positivity)
      hd.degree hd.rows hQD hper).trans (Real.exp_le_exp.mpr hAT)
  have hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp p ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp ((layerTailDegree m + 1 : ℕ) * p) :=
        (Real.exp_nat_mul p (layerTailDegree m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hST
  have he := Real.exp_le_exp.mpr hpT
  exact ⟨(jetAmbientIndex_card_le O J hd.nonneg hd.degree hd.rows
    (fun j => (hJ j).trans hpD)).trans hD3T,
    allocatedErrorKernel_exp_bounds B U b S η _ C V hT (hd.degree.trans hDT)
      (hd.axes.trans hDT) (hd.outputs.trans hDT) (fun j => (hd.rows j).trans hDT)
      (fun j => (hJ j).trans hpT) hη hA hK (fun j => (hC j).trans he) (fun j => (hV j).trans he)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

def allocatedProfileGainLog {A : Type*} [Semiring A] (m : ℕ) (D p w : A) : A :=
  D ^ 3 * ((m + 1 : ℕ) * p) + D * w

theorem allocatedProfileGainLog_nonneg (m : ℕ) {D p w : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hw : 0 ≤ w) :
    0 ≤ allocatedProfileGainLog m D p w := by
  unfold allocatedProfileGainLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem allocatedProfileGain_le_exp {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (hQ : ∀ j, (Fintype.card (Q j) : ℝ) ≤ D)
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1)) (Cm : ℝ≥0)
    {p w : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hM : (M : ℝ) ≤ Real.exp p) (hCm : (Cm : ℝ) ≤ Real.exp w) :
    (Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      Cm ^ Fintype.card (LayerSamplerAxis I n) : ℝ≥0) ≤
      Real.exp (allocatedProfileGainLog m D p w) := by
  have hper : (period : ℝ) ≤ Real.exp ((m + 1 : ℕ) * p) := by
    calc
      _ ≤ (M : ℝ) ^ (m + 1) := by exact_mod_cast hperiod
      _ ≤ Real.exp p ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul p (m + 1)).symm
  have hd := coefficientDeckPeriodCap_exp_bound O Q period h.nonneg (by positivity)
    h.degree h.rows hQ hper
  have hm := allocatedMaskPower_le_exp B h Cm.coe_nonneg hw hCm
  simp only [NNReal.coe_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
  exact (mul_le_mul hd hm (pow_nonneg Cm.coe_nonneg _) (Real.exp_pos _).le).trans_eq
    ((Real.exp_add _ _).symm)

theorem allocatedProfileError_mass_budget
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
    {T : Type*} [Fintype T] (select : T ↪ (Σ a : {a // ¬P a}, O a.val.1))
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j)
    {δ : ℝ≥0} {p e gain E A ε mesh : ℝ}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hA : 0 ≤ A)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (hAg : A ≤ Real.exp gain)
    (hε : ε ≤ physicalIdealErrorShare E gain)
    (hmesh : mesh ≤ physicalIdealErrorShare E (gain + allocatedIdealMeshEnvelope m D p e)) :
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬P a}, O a.val.1), R q.1.val.1)⁻¹‖₊ *
      (affineProductProfileLip (Σ a : {a // ¬P a}, O a.val.1) δ *
        NNReal.mk (Real.exp p) (Real.exp_pos p).le)
    let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
      (Real.exp p * (partitionedIdealRadius α m + 1)))
    A * (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
      ((2 * (Ro : ℝ) + 2) ^ Fintype.card T * ((Kp : ℝ) + Ki) * mesh)) ≤ Real.exp (-E) := by
  have hc := allocatedIdealGridAllowance_le_exp B h hp select
    (fun q => R q.1.val.1) (fun q => hR q.1.val.1) he
    (h.active_outputs B P) (fun q => hRi q.1.val.1) hδ
  dsimp only at hc ⊢
  have herr := physicalIdeal_three_errors_le
    (a := 0) (η := 0) (V := 0)
    (by norm_num) hA
    (mixedOutputGridAllowance_nonneg select (NNReal.coe_nonneg _) (by positivity))
    (by positivity) hAg hc (physicalIdealErrorShare_pos E 0).le hε hmesh
  simpa only [zero_mul, zero_add, mixedOutputGridAllowance, mul_assoc] using herr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedSiteErrorPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p w v : A) : A :=
  allocatedErrorPrimitiveLog m p + allocatedComparisonDimension m p * w + v

theorem allocatedSiteErrorPrimitiveLog_bounds (m : ℕ) {p w v : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    let D := allocatedComparisonDimension m p
    let T := allocatedSiteErrorPrimitiveLog m p w v
    0 ≤ T ∧ p ≤ T ∧ D ≤ T ∧ D ^ 3 ≤ T ∧
      (layerTailDegree m + 1 : ℕ) * p ≤ T ∧
      allocatedProfileGainLog m D p w + v ≤ T := by
  obtain ⟨hbase, hpbase, hDbase, hD3base, hSbase, hAbase⟩ :=
    allocatedErrorPrimitiveLog_bounds m hp
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hmask : 0 ≤ allocatedComparisonDimension m p * w := mul_nonneg hD hw
  dsimp only [allocatedSiteErrorPrimitiveLog, allocatedProfileGainLog]
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedSiteErrorPrimitive_constants
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1))
    (η CM Cf : ℝ≥0) (C V : Fin m → ℝ≥0) {p w v : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hη : η ≤ 1) (hM : (M : ℝ) ≤ Real.exp p) (hS : (S.value : ℝ) ≤ Real.exp p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hCM : (CM : ℝ) ≤ Real.exp w) (hCf : (Cf : ℝ) ≤ Real.exp v) :
    let T := allocatedSiteErrorPrimitiveLog m p w v
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ T ∧
      (allocatedErrorKernelCap B U b S (O := O) η A V : ℝ) ≤ Real.exp (allocatedErrorKernelLog T) ∧
      (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp (allocatedErrorKernelLog T) := by
  let D := allocatedComparisonDimension m p
  let T := allocatedSiteErrorPrimitiveLog m p w v
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  obtain ⟨hT, hpT, hDT, hD3T, hST, hAT⟩ := allocatedSiteErrorPrimitiveLog_bounds m hp hw hv
  have hpD : p ≤ D := (allocatedComparisonDimension_bounds m hp).2.2.1
  have hQD (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans ((hJ j).trans hpD)
  have hgain := allocatedProfileGain_le_exp B hd hQD M period hperiod CM hp hw hM hCM
  have hA : ((Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf : ℝ≥0) : ℝ) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (allocatedProfileGainLog m D p w) * Real.exp v :=
        mul_le_mul hgain hCf Cf.coe_nonneg (Real.exp_pos _).le
      _ = Real.exp (allocatedProfileGainLog m D p w + v) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hAT
  have hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp p ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp ((layerTailDegree m + 1 : ℕ) * p) :=
        (Real.exp_nat_mul p (layerTailDegree m + 1)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hST
  have he := Real.exp_le_exp.mpr hpT
  exact ⟨(jetAmbientIndex_card_le O J hd.nonneg hd.degree hd.rows
    (fun j => (hJ j).trans hpD)).trans hD3T,
    allocatedErrorKernel_exp_bounds B U b S η _ C V hT (hd.degree.trans hDT)
      (hd.axes.trans hDT) (hd.outputs.trans hDT) (fun j => (hd.rows j).trans hDT)
      (fun j => (hJ j).trans hpT) hη hA hK (fun j => (hC j).trans he) (fun j => (hV j).trans he)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def profileReferenceErrorLog {A : Type*} [Semiring A] (P E : A) : A :=
  coefficientErrorSpatialLog P + E + 4

noncomputable def profileReferenceAccuracy (P E : ℝ) : ℝ :=
  Real.exp (-profileReferenceErrorLog P E)

theorem profileReferenceAccuracy_bounds {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < profileReferenceAccuracy P E ∧ profileReferenceAccuracy P E ≤ 1 ∧
      (profileReferenceAccuracy P E)⁻¹ = Real.exp (profileReferenceErrorLog P E) := by
  have hs := coefficientErrorSpatialLog_nonneg hP
  have hl : 0 ≤ profileReferenceErrorLog P E := by unfold profileReferenceErrorLog; linarith
  exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl), by
    rw [profileReferenceAccuracy, ← Real.exp_neg, neg_neg]⟩

theorem profileReferenceAccuracy_normalized_error {P E S M δ ε Z : ℝ}
    (hS0 : 0 ≤ S) (hS : S ≤ Real.exp (coefficientErrorSpatialLog P))
    (hM : M ≤ profileReferenceAccuracy P E)
    (hδ : δ ≤ profileReferenceAccuracy P E) (hε : ε ≤ profileReferenceAccuracy P E)
    (hZ : 1 / 2 ≤ Z) :
    S * (M + 2 * δ + ε) / Z ≤ Real.exp (-E) := by
  have ha : 0 < profileReferenceAccuracy P E := Real.exp_pos _
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  apply coefficientError_normalized_exp_bound (E := E) ?_ hZ
  calc
    _ ≤ S * (4 * profileReferenceAccuracy P E) := mul_le_mul_of_nonneg_left (by linarith) hS0
    _ ≤ Real.exp (coefficientErrorSpatialLog P) * (4 * profileReferenceAccuracy P E) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = 4 * Real.exp (-(E + 1) - 3) := by
      unfold profileReferenceAccuracy profileReferenceErrorLog
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp 3 * Real.exp (-(E + 1) - 3) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_profileReferenceErrorLog_bound :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P E : ℝ}, 0 ≤ P → 0 ≤ E →
      profileReferenceErrorLog P E ≤ (P + E + a) ^ a := by
  let poly : Polynomial ℕ := profileReferenceErrorLog Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P E hP hE
  have hmono : profileReferenceErrorLog P E ≤ profileReferenceErrorLog (P + E) (P + E) := by
    have hPQ : P ≤ P + E := le_add_of_nonneg_right hE
    have hEQ : E ≤ P + E := le_add_of_nonneg_left hP
    unfold profileReferenceErrorLog coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  apply hmono.trans
  simpa [poly, profileReferenceErrorLog, coefficientErrorSpatialLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, Polynomial.eval₂_pow] using hbound (P + E) (add_nonneg hP hE)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedReferenceIdealError {A : Type*} [Semiring A]
    (m : ℕ) (D P E : A) : A :=
  profileReferenceErrorLog P E + D ^ 3 * ((m + 1 : ℕ) * P)

theorem allocatedReferenceIdealError_nonneg (m : ℕ) {D P E : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ allocatedReferenceIdealError m D P E := by
  have hs := coefficientErrorSpatialLog_nonneg hP
  unfold allocatedReferenceIdealError profileReferenceErrorLog
  positivity

theorem allocatedReferenceIdealError_add_mask (m : ℕ) (D P E w : ℝ) :
    allocatedReferenceIdealError m D P E + D * w =
      profileReferenceErrorLog P E + allocatedProfileGainLog m D P w := by
  unfold allocatedReferenceIdealError allocatedProfileGainLog
  ring

theorem allocatedReferenceIdealError_share (m : ℕ) (D P E w : ℝ) :
    physicalIdealErrorShare (allocatedReferenceIdealError m D P E) (D * w) =
      physicalIdealErrorShare (profileReferenceErrorLog P E) (allocatedProfileGainLog m D P w) := by
  unfold physicalIdealErrorShare
  rw [allocatedReferenceIdealError_add_mask]

theorem allocatedReferenceIdealLength_mesh (m : ℕ) {D P E p e w : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hp : 0 ≤ p) :
    profileReferenceErrorLog P E + (allocatedProfileGainLog m D P w +
        allocatedIdealMeshEnvelope m D p e) + 3 ≤
      allocatedPhysicalIdealLengthEnvelope m D p e w (allocatedReferenceIdealError m D P E) := by
  have htarget := allocatedReferenceIdealError_nonneg m hD hP hE
  have ht := allocatedTestLengthEnvelope_nonneg m hD hp
    (show 0 ≤ allocatedReferenceIdealError m D P E + 3 by positivity)
  rw [show profileReferenceErrorLog P E + (allocatedProfileGainLog m D P w +
      allocatedIdealMeshEnvelope m D p e) + 3 =
      allocatedReferenceIdealError m D P E + D * w + allocatedIdealMeshEnvelope m D p e + 3 by
    rw [allocatedReferenceIdealError_add_mask]
    ring]
  exact le_add_of_nonneg_left ht

open scoped NNReal

variable {Ω α : Type*} [Fintype Ω] [Fintype α]
variable {B O : Ω → Type*} [∀ a, Fintype (B a)] [∀ a, Fintype (O a)]

theorem allocatedReferenceIdealSmoothing_eq (h : Ω → ℕ) (A T : ℝ≥0)
    (m : ℕ) (D P E w : ℝ) :
    physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T
        (allocatedReferenceIdealError m D P E) (D * w) =
      physicalIdealSmoothingLog (B := B) (O := O) (α := α) h A T
        (profileReferenceErrorLog P E) (allocatedProfileGainLog m D P w) := by
  unfold physicalIdealSmoothingLog
  rw [allocatedReferenceIdealError_add_mask]

end Erdos3.VectorPolynomial

end

end OAI
