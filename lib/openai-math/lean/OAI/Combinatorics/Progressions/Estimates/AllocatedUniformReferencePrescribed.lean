import OAI.Combinatorics.Progressions.Estimates.AllocatedReferencePrescribeData

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable (m dim : ℕ)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

theorem exists_uniform_allocated_reference_actual_ideal :
    ∃ K : ℕ, 2 ≤ K ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (_hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (_hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (_hLip : LipschitzWith A ψ) (_hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (_hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (_hPsp : 0 ≤ Psp) (_hE : 0 ≤ E),
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a)) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedReferenceActualIdealAt.{uG,uI,uB,uJ,uQ,uX} (G := G) (dim := dim) B D Psp E e gainLog t δ K := by
  obtain ⟨K, hK, hwindow⟩ :=
    exists_allocated_reference_ideal_sampling.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨K, hK, ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition D Psp E hdim hPsp hE
  let target := profileReferenceErrorLog Psp E
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  let gainLog := allocatedProfileGainLog m D Psp w
  have hgainLog : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n) A T htarget hgainLog
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcontrol⟩ :=
    exists_allocated_actual_profile_sampling_data (G := G) (α := Fin dim) (O := jets) B
      ψ hψ hrange hzero hone A T hLip hTransition hdim htarget hPsp hw
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro hmPsp hdimPsp hGPsp J _ U b R σ hR hσ hσt S x Mk hMk selection hx hqDim s hA block hi
    _ hb o Q _ bW d _ C V hC hV ν _ _ modulus _ hperiod hperiodSp X _ _ q hq _ reference residue
    N hN W τ ξ ρ hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift hbudget base cells hmass p hp hm
    pNum lengthLog Rrank hpNum hPspNum herrorNum hRP hRi hσi hcount hlengthLog hlength hmeshLarge hCp hVp
    hX hdimNum hτP hstride spatialMesh hspatialMesh hMkPsp hperiodM Dsp hXPsp hDsp hWscale
    input Pout hsize hrank hRank test htest Z hZ
  let Cm : ℝ≥0 := ⟨(layerKernelIndexBound m Mk : ℝ), Nat.cast_nonneg _⟩
  have hCmw : (Cm : ℝ) ≤ Real.exp w := layerKernelIndexBound_le_exp m hMkPsp
  have hMkNum : (Mk : ℝ) ≤ Real.exp pNum := hMkPsp.trans (Real.exp_le_exp.mpr hPspNum)
  have hgrid := allocatedIdealGridEnvelope_nonneg m hdim.nonneg hpNum he
  have hD : 0 ≤ D := hdim.nonneg
  have hmeshCost : 0 ≤ gainLog + allocatedIdealMeshEnvelope m D pNum e := by
    unfold allocatedIdealMeshEnvelope
    positivity
  have hmesh0 := (physicalIdealErrorShare_pos target (gainLog + allocatedIdealMeshEnvelope m D pNum e)).le
  have hmesh1 := physicalIdealErrorShare_le_one htarget hmeshCost
  have hmesh := physicalIdealErrorShare_scale_mesh (layerTailDegree m) htarget hmeshCost hmeshLarge
  have haccuracy := profileReferenceAccuracy_bounds hPsp hE
  have hδF : (profileReferenceAccuracy Psp E)⁻¹ ≤ Real.exp pNum :=
    haccuracy.2.2.le.trans (Real.exp_le_exp.mpr herrorNum)
  obtain ⟨hPout, hdata⟩ := hcontrol U b hR hσ hσt S x jetRows
    (fun _ => Subtype.val_injective) (fun _ z => z.property) block s hA hMk hi
    hpNum hMkNum hRP hRi hσi hcount hmesh0 hmesh1 hmesh le_rfl hb o bW modulus hperiodM hMkPsp
    Cm hCmw hlengthLog hlength C V hCp hVp hδF
  have haccuracyPout : 1 / profileReferenceAccuracy Psp E ≤ Real.exp Pout := by
    simpa only [one_div] using hδF.trans (Real.exp_le_exp.mpr hPout)
  have hperiodPsp := coefficientErrorPeriod_exp_sq hPsp hmPsp hMkPsp hperiodM
  exact hwindow B U b hR hσ S x hMk selection hx hqDim s hA δ hb o bW d C V hC hV ν
    modulus hperiod hperiodSp q hq reference residue N hN hW hτ hξ hξ1 hρ hsizeSp hρ8 hρshift
    hbudget base cells hmass p hp hm (hpNum.trans hPout) (hX.trans hPout) (hdimNum.trans hPout)
    (hτP.trans (Real.exp_le_exp.mpr hPout)) (fun a => (hstride a).trans (Real.exp_le_exp.mpr hPout))
    haccuracy.1 haccuracyPout hsize hrank hRank spatialMesh hspatialMesh
    haccuracy.1 hPsp hMkPsp hperiodPsp hdimPsp hGPsp hXPsp hDsp hWscale le_rfl le_rfl le_rfl
    hdata test htest Z hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable (m dim : ℕ)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

theorem exists_uniform_allocated_reference_prescribed_flexible :
    ∃ K : ℕ, 2 ≤ K ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (_hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (_hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (_hLip : LipschitzWith A ψ) (_hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (_hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (_hPsp : 0 ≤ Psp) (_hE : 0 ≤ E),
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a)) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∀ (e' t' : ℝ), e ≤ e' → t' ≤ t →
          AllocatedReferencePrescribedIdealAt.{uG,uI,uB,uJ,uQ,uX}
            (G := G) (dim := dim) B D Psp E e' t' δ K := by
  obtain ⟨K, hK, hactual⟩ :=
    exists_uniform_allocated_reference_actual_ideal.{uG,uI,uB,uJ,uQ,uX} m dim
  obtain ⟨Ktail, hKtail, htail⟩ :=
    exists_allocated_ideal_reference_tail.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨max K Ktail, hK.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition D Psp E hdim hPsp hE
  have htarget : 0 ≤ profileReferenceErrorLog Psp E := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    hactual B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  intro e' t' hee htt
  have he' : 0 ≤ e' := he.trans hee
  have hflex := hcompare.mono_smoothing B hdim.nonneg he hgain hee htt
  exact allocatedReferenceChosenIdealAt_prescribeData B hdim hPsp hE he' hK hKtail htail
    (allocatedReferenceActualIdealAt_chooseScale B hdim hPsp hE he' hflex)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

variable (m dim : ℕ)
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

theorem exists_uniform_allocated_reference_prescribed_ideal :
    ∃ K : ℕ, 2 ≤ K ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ) (_hψ : ContDiff ℝ ∞ ψ) (_hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (_hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (_hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (_hLip : LipschitzWith A ψ) (_hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (_hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (_hPsp : 0 ≤ Psp) (_hE : 0 ≤ E),
      let target := profileReferenceErrorLog Psp E
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a)) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          AllocatedReferencePrescribedIdealAt.{uG,uI,uB,uJ,uQ,uX} (G := G) (dim := dim) B D Psp E e t δ K := by
  obtain ⟨K, hK, hactual⟩ :=
    exists_uniform_allocated_reference_actual_ideal.{uG,uI,uB,uJ,uQ,uX} m dim
  obtain ⟨Ktail, hKtail, htail⟩ :=
    exists_allocated_ideal_reference_tail.{uG,uI,uB,uJ,uQ,uX} m dim
  refine ⟨max K Ktail, hK.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition D Psp E hdim hPsp hE
  have htarget : 0 ≤ profileReferenceErrorLog Psp E := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    hactual B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE
  refine ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, ?_⟩
  exact allocatedReferenceChosenIdealAt_prescribeData B hdim hPsp hE he hK hKtail htail
    (allocatedReferenceActualIdealAt_chooseScale B hdim hPsp hE he hcompare)

end Erdos3.VectorPolynomial

end

end OAI
