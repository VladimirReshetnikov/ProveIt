import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealReferenceInsertion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

def AllocatedProfileSamplingData
    (f g : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S) →
      ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) → ℝ) → ℝ)
    (A : ℝ≥0) (C V : Fin m → ℝ≥0) (δF Merr L P : ℝ) : Prop :=
  ∃ Cf Cg Kf Kg : ℝ≥0,
    (∀ u, LipschitzWith Kf (f u)) ∧ (∀ u, LipschitzWith Kg (g u)) ∧
    (∀ u z, |f u z| ≤ Cf) ∧ (∀ u z, |g u z| ≤ Cg) ∧
    0 ≤ L ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧ δF⁻¹ ≤ Real.exp L ∧
    (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L ∧
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P ∧
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ≤ Real.exp P ∧
    (∀ u, Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun z => |f u z - g u z|))
      (allocatedLongJetReference B U b S O)) ∧
    (∀ u, (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f u v - g u v|) z
      ∂allocatedLongJetReference B U b S O) ≤ Merr)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable (f g : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
    ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) → ℝ) → ℝ)
variable (A : ℝ≥0) (C V : Fin m → ℝ≥0)

theorem allocatedProfileSamplingData_mono {δF Merr Merr' L P P' : ℝ}
    (h : AllocatedProfileSamplingData B U b S f g A C V δF Merr L P)
    (hM : Merr ≤ Merr') (hP : P ≤ P') :
    AllocatedProfileSamplingData B U b S f g A C V δF Merr' L P' := by
  obtain ⟨Cf, Cg, Kf, Kg, hf, hg, hfb, hgb, hL, hamb, hδL,
    hLip, hfreq, hcoeff, hi, hmass⟩ := h
  exact ⟨Cf, Cg, Kf, Kg, hf, hg, hfb, hgb, hL, hamb, hδL, hLip,
    hfreq.trans (Real.exp_le_exp.mpr hP), hcoeff.trans (Real.exp_le_exp.mpr hP),
    hi, fun u => (hmass u).trans hM⟩

theorem allocatedProfileSamplingData_reference_accuracy {δF L P P' Psp E : ℝ}
    (h : AllocatedProfileSamplingData B U b S f g A C V δF (profileReferenceAccuracy Psp E) L P)
    (hPsp : 0 ≤ Psp) (hP : P ≤ P') :
    AllocatedProfileSamplingData B U b S f g A C V δF (Real.exp (-(E + 3))) L P' := by
  apply allocatedProfileSamplingData_mono B U b S f g A C V h _ hP
  apply Real.exp_le_exp.mpr
  have hs := coefficientErrorSpatialLog_nonneg hPsp
  change -(coefficientErrorSpatialLog Psp + E + 4) ≤ -(E + 3)
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_actual_profile_sampling_data
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D E p₀ w : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hE : 0 ≤ E) (hp₀ : 0 ≤ p₀) (hw : 0 ≤ w) :
    let gainLog := allocatedProfileGainLog m D p₀ w
    let ε := physicalIdealErrorShare E gainLog
    let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
      (α := α) hLayer A T E gainLog
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        {mesh : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (_hmeshBudget : mesh ≤ physicalIdealErrorShare E (gainLog + allocatedIdealMeshEnvelope m D P e))
        {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
        (_hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (_o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (_bW : ∀ j, Module.Basis (Q j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (period : ℕ) (_hperiodM : period ≤ M ^ (m + 1)) (_hM₀ : (M : ℝ) ≤ Real.exp p₀)
        (Cm : ℝ≥0) (_hCmw : (Cm : ℝ) ≤ Real.exp w)
        {lengthLog δF : ℝ} (_hlengthLog : 0 ≤ lengthLog)
        (_hlength : (S.value : ℝ) ≤ Real.exp lengthLog)
        (C V : Fin m → ℝ≥0)
        (_hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
        (_hδF : δF⁻¹ ≤ Real.exp P),

      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let proxy := fun u => allocatedContinuousLongJetProxy B U basis S x u rows s hA
      let gain := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
        Cm ^ Fintype.card (LayerSamplerAxis I n)
      let input := allocatedActualProfileInput m D P e gainLog lengthLog
      let L := allocatedProfileFourierInput input
      let Pout := allocatedProfileFourierOutput input
      P ≤ Pout ∧ AllocatedProfileSamplingData B U basis S proxy (fun _ => ideal)
        gain C V δF (Real.exp (-E)) L Pout := by
  dsimp only
  let gainLog := allocatedProfileGainLog m D p₀ w
  have hgainLog : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hp₀ hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
    (α := α) hLayer A T E gainLog
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg hLayer A T hE hgainLog
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcontrol⟩ := exists_allocated_actual_profile_control
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition
    (physicalIdealErrorShare_pos E gainLog)
  have hδe : (δ : ℝ)⁻¹ ≤ Real.exp e := by
    rw [hδeq]
    exact physicalIdeal_smoothing_inverse_le_exp hLayer (fun a => Nat.succ_pos _)
      A T hE hgainLog
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount mesh hmesh0 hmesh1 hmesh hmeshBudget
    Q _ hb o bW period hperiodM hM₀ Cm hCmw lengthLog δF hlengthLog hlength C V hC hV hδF
  let gain := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
    Cm ^ Fintype.card (LayerSamplerAxis I n)
  have hdims := allocatedProfile_dimensions U basis o B hdim hb bW
  have hgain := allocatedProfileGain_le_exp B hdim hdims.2 M period hperiodM Cm hp₀ hw hM₀ hCmw
  have hfourier := allocatedActualProfile_fourier_budget B hdim U basis S
    hP he hgainLog hlengthLog hdims.1 (fun j => (hR j).le) hRi hδe gain hgain hlength C V hC hV hδF
  obtain ⟨hL, hPout, hamb, hδL, hLipOut, hfreq, hcoeff⟩ := hfourier
  have hprofile (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
      (allocatedPrincipalSides B U basis S)) :=
    hcontrol U basis hR hσ hσt S x u rows hrows hcard block s hA
      hM hi hP hMP hRP hRi hσi hcount hmesh0 hmesh1 hmesh
  let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
  let Cp : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
  let Ci : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
    R q.1.val.1)⁻¹‖₊ * δ⁻¹ ^ Fintype.card (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1)
  let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound * bound ^ Fintype.card (LayerSamplerAxis I n)
  let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
    R q.1.val.1)⁻¹‖₊ *
    (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
      NNReal.mk (Real.exp P) (Real.exp_pos P).le)
  refine ⟨hPout, Cp, Ci, Kp, Ki, (fun u => (hprofile u).1), (fun u => (hprofile u).2.1),
    (fun u => (hprofile u).2.2.1), (fun u => (hprofile u).2.2.2.1), hL, hamb, hδL,
    hLipOut, hfreq, hcoeff, (fun u => (hprofile u).2.2.2.2.1), ?_⟩
  intro u
  have hbudget := allocatedProfileError_mass_budget B hdim
    (allocatedGridAxis (I := I) U basis S.value) (allocatedLongIntegerSelect B U basis S (O := O))
    R (fun j => (hR j).le) hP he gain.coe_nonneg hRi hδe hgain le_rfl hmeshBudget
  exact (mul_le_mul_of_nonneg_left (hprofile u).2.2.2.2.2 gain.coe_nonneg).trans hbudget

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

def allocatedProfileAccuracyBudget {R : Type*} [Semiring R] (L P a : R) : R :=
  P + (2 * (L + a) + 2) ^ 4 + 2 * (L + a) * (2 * (L + a) + 2) ^ 4

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} {O : Fin m → Type*} [∀ j, Fintype (O j)]

variable (f g : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
    ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) → ℝ) → ℝ)
variable (A : ℝ≥0) (C V : Fin m → ℝ≥0)

theorem allocatedProfileSamplingData_accuracy {δF δF' Merr L P a : ℝ}
    (h : AllocatedProfileSamplingData B U b S f g A C V δF Merr L P)
    (ha : 0 ≤ a) (hδ : δF'⁻¹ ≤ Real.exp a) :
    AllocatedProfileSamplingData B U b S f g A C V δF' Merr (L + a)
      (allocatedProfileAccuracyBudget L P a) := by
  obtain ⟨Cf, Cg, Kf, Kg, hf, hg, hfb, hgb, hL, hamb, _hδL,
    hLip, hfreq, hcoeff, hi, hmass⟩ := h
  have hLL : L ≤ L + a := le_add_of_nonneg_right ha
  have hLa : 0 ≤ L + a := add_nonneg hL ha
  have hfreq0 : 0 ≤ (2 * (L + a) + 2) ^ 4 := by positivity
  have hterm : 0 ≤ 2 * L * (2 * L + 2) ^ 4 := by positivity
  have hterm' : 0 ≤ 2 * (L + a) * (2 * (L + a) + 2) ^ 4 := by positivity
  have hP : 0 ≤ P := (by positivity : 0 ≤ (2 * L + 2) ^ 4).trans (Real.exp_le_exp.mp hfreq)
  have hcap : (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ) ≤ Real.exp P := by
    calc
      _ = 1 * (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ) := (one_mul _).symm
      _ ≤ Real.exp (2 * L * (2 * L + 2) ^ 4) *
          (allocatedProfileErrorCap B U b S (O := O) A Cf Cg V : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.one_le_exp hterm) (NNReal.coe_nonneg _)
      _ ≤ Real.exp P := hcoeff
  refine ⟨Cf, Cg, Kf, Kg, hf, hg, hfb, hgb, hLa, hamb.trans hLL,
    hδ.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hL)),
    hLip.trans (Real.exp_le_exp.mpr hLL), ?_, ?_, hi, hmass⟩
  · apply Real.exp_le_exp.mpr
    unfold allocatedProfileAccuracyBudget
    linarith only [hP, hterm']
  · calc
      _ ≤ Real.exp (2 * (L + a) * (2 * (L + a) + 2) ^ 4) * Real.exp P :=
        mul_le_mul_of_nonneg_left hcap (Real.exp_pos _).le
      _ = Real.exp (2 * (L + a) * (2 * (L + a) + 2) ^ 4 + P) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        unfold allocatedProfileAccuracyBudget
        linarith only [hfreq0]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable (m dim : ℕ)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem exists_allocated_reference_ideal_sampling :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
    (_hqDim : dim ≤ m + 1)
    (s : ∀ j, jets j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (jetRows j)).submatrix id (s j)).det ≠ 0)
    (δ : ℝ≥0)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (modulus : ℕ) [NeZero modulus]
    (_hperiod : ∀ j, integerScalarLattice (jets j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (jetRows j)).mulVecLin.range)
    (_hperiodSp : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] [DecidableEq X]
    (q : X → ℕ) (_hq : ∀ t, 0 < q t)
    [NeZero (residueRefinedPeriod modulus q)]
    (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
      (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
        (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
      ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (N : X → ℕ) (_hN : ∀ t, 0 < N t)
    {W τ ξ ρ : ℝ} (_hW : 0 ≤ W) (_hτ : 0 < τ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hρ : 0 < ρ)
    (_hsizeSp : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (_hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (_hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {P Rrank ε : ℝ} (_hP : 0 ≤ P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P)
    (_hτP : 1 / τ ≤ Real.exp P) (_hstride : ∀ t, (q t : ℝ) ≤ Real.exp P)
    (_hε : 0 < ε) (_hεP : 1 / ε ≤ Real.exp P)
    (_hsize : ∀ t, Real.exp ((P + K) ^ K) ≤ (N t : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (p j))
    (_hRank : Real.exp ((P + K) ^ K) ≤ Rrank)
    (spatialMesh : ℝ) (_hspatialMesh : 0 < spatialMesh)
    {δf Merr L Psp E Dsp : ℝ} (_hδf : 0 < δf)
    (_hPsp : 0 ≤ Psp) (_hMPsp : (Mk : ℝ) ≤ Real.exp Psp)
    (_hperiodPsp : (modulus : ℝ) ≤ Real.exp (Psp ^ 2))
    (_hdimPsp : ((dim + 1 : ℕ) : ℝ) ≤ Psp) (_hGPsp : (Fintype.card G : ℝ) ≤ Psp)
    (_hXPsp : (Fintype.card X : ℝ) ≤ Psp)
    (_hDsp : Dsp ≤ Real.exp Psp) (_hWscale : W ≤ Dsp * (S.value : ℝ))
    (_hMerr : Merr ≤ profileReferenceAccuracy Psp E)
    (_hδfBudget : δf ≤ profileReferenceAccuracy Psp E)
    (_hεBudget : ε ≤ profileReferenceAccuracy Psp E),
    let Cm : ℝ≥0 := ⟨(layerKernelIndexBound m Mk : ℝ), Nat.cast_nonneg _⟩
    let gain := Real.toNNReal (coefficientDeckPeriodCap jets Q modulus) *
      Cm ^ Fintype.card (LayerSamplerAxis I n)
    AllocatedProfileSamplingData B U b S
      (fun u => allocatedContinuousLongJetProxy B U b S x u jetRows s hA)
      (fun _ => physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim))
        (layerSamplerDegree I n) (allocatedGridAxis (I := I) U b S.value)
        (fun a => jetRows a.val.1) (fun a => R a.1) (fun a => hR a.1) δ)
      gain C V δf Merr L P →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ w, ‖test w‖ ≤ 1) →
    ∀ Z : ℝ, 1 / 2 ≤ Z →
    ‖allocatedRefinedTupleReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus s hA q reference residue hb o bW d
        N _hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm) test Z -
      allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
        B U b hR hσ S x jetRows X hMk selection hx modulus q reference residue hb o bW d
        N _hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm) test Z δ‖ ≤ Real.exp (-E) := by
  obtain ⟨K, hK, hwindow⟩ := exists_allocated_reference_profile_window_bound m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ hR hσ S x Mk hMk selection hx hqDim s hA δ _ hb o Q _ bW d _ C V hC hV ν _ _
    modulus _ hperiod hperiodSp X _ _ q hq _ reference residue N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm P Rrank ε hP hX hdim hτP hstride hε hεP hsize hrank hRank
    spatialMesh hspatialMesh δf Merr L Psp E Dsp hδf hPsp hMPsp hperiodPsp hdimPsp hGPsp hXPsp
    hDsp hWscale hMerr hδfBudget hεBudget Cm gain hdata test htest Z hZ
  obtain ⟨Cf, Cg, Kf, Kg, hf, hg, hfb, hgb, hL, hamb, hδL, hLip, hfreq, hcoeff, hi, hmassProfile⟩ := hdata
  have hCm : 1 ≤ (Cm : ℝ) := by
    change (1 : ℝ) ≤ (layerKernelIndexBound m Mk : ℝ)
    exact_mod_cast Nat.succ_le_of_lt (pow_pos hMk (m * 2 ^ (m + 1)))
  have hmasks u r j z := allocatedIntegerKernelMask_bound B U b S x jetRows hMk selection hx
    (by simpa only [Fintype.card_fin] using hqDim) (fun _ => Subtype.val_injective)
    (fun _ z => z.property) j modulus (residue u r j) z
  have hwindowBound := hwindow B U b hR hσ S x hMk selection hx hb o bW d C V hC hV ν
    modulus hperiod hperiodSp q hq reference residue N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm hP hX hdim hτP hstride hε hεP hsize hrank hRank
    spatialMesh hspatialMesh Cm hCm hmasks _ _ Cf Cg Kf Kg hf hg hfb hgb
    hδf hL hamb hδL hLip hfreq hcoeff hi Merr hmassProfile test htest
  have hS1 : 1 ≤ (S.value : ℝ) := by exact_mod_cast S.positive
  have hsp := coefficientErrorSpatialFactor_exp_bound dim X selection hPsp hMk hMPsp
    hperiodPsp hdimPsp hGPsp hXPsp hS1 hW hDsp hWscale
  apply allocatedRefinedTupleReference_ideal_exp_error B U b hR hσ S x jetRows X hMk selection hx modulus
    s hA q reference residue hb o bW d N hW spatialMesh base cells (physicalCubeEuclideanSample U d p hm)
    test Z δ hsp.1 hsp.2 hMerr hδfBudget hεBudget hZ
  have hactual : allocatedRefinedReferenceProfile B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d =
      fun u r => allocatedCoveredProfileDensity B U b hR hσ S x u (reference u r) jetRows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x jetRows modulus (residue u r)
          (allocatedContinuousLongJetProxy B U b S x u jetRows s hA)) := by
    funext u r
    exact allocatedRefinedReferenceProfile_as_covered B U b hR hσ S x jetRows X modulus s hA q reference residue hb o bW d u r
  rw [hactual]
  unfold allocatedRefinedIdealProfile
  intro u r
  simpa only [mul_assoc] using hwindowBound u r

end Erdos3.VectorPolynomial

end

end OAI
