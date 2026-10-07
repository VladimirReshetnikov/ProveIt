import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uGeom uCover uSpace

theorem exists_uniform_allocated_original_mesh (m dim : ℕ) :
    ∃ A T Kproj : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ 2 ≤ Kproj ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
      {D Psp E e t : ℝ} {δ : ℝ≥0} {Kideal : ℕ},
      AllocatedComparisonDimensions (G := G) B (Fin dim)
        (fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)) D →
      0 ≤ Psp → 0 ≤ E → 0 ≤ e → t ≤ 1 → 2 ≤ Kideal →
      AllocatedReferencePrescribedIdealAt.{uG,uI,uB,uGeom,uCover,uSpace}
        (G := G) (dim := dim) B D Psp (E + 4) e t δ Kideal →
      AllocatedOriginalPrescribedMeshAt.{uG,uI,uB,uGeom,uCover,uSpace}
        (G := G) (dim := dim) B D Psp E e t δ A T Kproj Kideal := by
  obtain ⟨A, T, Kproj, hA, hT, hKproj, hfamily⟩ :=
    exists_allocated_ideal_density_source_family.{uSpace,uG,uI,uB,uGeom} m dim
  refine ⟨A, T, Kproj, hA, hT, hKproj, ?_⟩
  intro G _ _ I _ n B _ D Psp E e t δ Kideal hdim hPsp hE he ht1 hKideal hselected
  exact allocatedReferencePrescribedIdealAt_original_mesh_of_family B
    hdim hPsp hE he ht1 hKideal hselected hT hKproj hfamily

theorem exists_uniform_allocated_common_residue_weighted_original_mesh (m dim : ℕ) :
    ∃ K A₀ T₀ Kproj : ℕ, 2 ≤ K ∧ 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
    ∀ {G : Type uG} [Fintype G] [DecidableEq G]
      {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
    (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → (∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) →
    (∀ t, |t| ≤ 1 → ψ t = 0) → (∀ t, 2 ≤ |t| → ψ t = 1) →
    ∀ A T : ℝ≥0, LipschitzWith A ψ → LipschitzWith T Real.smoothTransition →
    ∀ {p Psp E : ℝ}, 0 ≤ p → 0 ≤ Psp → 0 ≤ E →
    dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ Psp → p ≤ Psp →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      let D := allocatedComparisonDimension m p
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1))
        (α := Fin dim) (layerSamplerDegree I n) A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1)) (α := Fin dim) (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => BoundedBooleanJet (Fin dim) (a.1.val + 1)) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
          (layerSamplerDegree I n)
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
            AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uGeom,uCover,uSpace} (G := G) (dim := dim)
              B p Psp E e t δ A₀ T₀ Kproj K := by
  obtain ⟨K, hK, hreference⟩ :=
    exists_uniform_allocated_reference_prescribed_ideal.{uG,uI,uB,uGeom,uCover,uSpace} m dim
  obtain ⟨A₀, T₀, Kproj, hA₀, hT₀, hKproj, hfamily⟩ :=
    exists_allocated_ideal_density_source_family.{uSpace,uG,uI,uB,uGeom} m dim
  refine ⟨K, A₀, T₀, Kproj, hK, hA₀, hT₀, hKproj, ?_⟩
  intro G _ _ I _ n B _ ψ hψ hrange hzero hone A T hLip hTransition p Psp E
    hp hPsp hE hdim hmPsp hpPsp hvars hI hn
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let jetRows := fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim))
  have hdimensions := allocatedComparisonDimensions_of_primitive B jetRows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  have hE4 : 0 ≤ E + 4 := by linarith
  have htarget : 0 ≤ profileReferenceErrorLog Psp (E + 4) := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    unfold profileReferenceErrorLog
    linarith
  have hw : 0 ≤ (m * 2 ^ (m + 1) : ℕ) * Psp := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdimensions.nonneg hPsp hw
  have he := physicalIdealSmoothingLog_nonneg (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    (layerSamplerDegree I n) A T htarget hgain
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hcompare⟩ :=
    hreference B
      ψ hψ hrange hzero hone A T hLip hTransition hdimensions hPsp hE4
  have horiginal := allocatedReferencePrescribedIdealAt_original_mesh_of_family B
    hdimensions hPsp hE he ht1 hK hcompare hT₀ hKproj hfamily
  exact ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedCommonOriginalMeshAt_residue_weighted B
      (allocatedOriginalPrescribedMeshAt_commonScale B hp hPsp hE hdim hmPsp hpPsp hvars horiginal)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq

section Data

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "hLayer" => layerSamplerDegree I n

def AllocatedUniformCommonCoverData (p P E : ℝ) (hP : 0 ≤ P) (A T : ℝ≥0)
    (A₀ T₀ Kproj Kideal Ksite : ℕ) : Prop :=
  let D := allocatedComparisonDimension m p
  let target := profileReferenceErrorLog P (E + 1 + 4)
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * P
  let gainLog := allocatedProfileGainLog m D P w
  let ε := physicalIdealErrorShare target gainLog
  let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) hLayer A T target gainLog
  let eTail := physicalIdealTailLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
    (α := Fin dim) G (G × Option (Fin dim)) hLayer A T m target gainLog
  let t := booleanMassPerturbationScale (B := B)
    (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
    ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
    (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
    A T m 1 (ε / 2)
  0 ≤ e ∧ 0 ≤ eTail ∧ 0 < t ∧ t ≤ 1 ∧ t⁻¹ ≤ Real.exp eTail ∧
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
      AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite ∧
      AllocatedCommonGenuineCoverAt.{uG,uI,uB,uJ,uQ,uX}
        (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite

end Data

theorem exists_uniform_common_cover :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∀ m dim : ℕ, ∃ A₀ T₀ Kproj Kideal Ksite : ℕ,
      2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧ 2 ≤ Kideal ∧ 2 ≤ Ksite ∧
      ∀ {G : Type uG} [Fintype G] [DecidableEq G]
        {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
        (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {p P E : ℝ}, 0 ≤ p → ∀ hP : 0 ≤ P, 0 ≤ E →
        dim ≤ m + 1 → ((m + 2 : ℕ) : ℝ) ≤ P → p ≤ P →
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
        (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
        (∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) →
        AllocatedUniformCommonCoverData.{uG,uI,uB,uJ,uQ,uX}
          (G := G) (dim := dim) B p P E hP A scalarSourceTransitionBound A₀ T₀ Kproj Kideal Ksite := by
  obtain ⟨A, hA, ψ, hψ, hrange, hzero, hone, hLip⟩ := exists_smooth_sublevel_cutoff
  refine ⟨A, hA, ?_⟩
  intro m dim
  obtain ⟨A₀, T₀, Kproj, hA₀, hT₀, hKproj, horiginal⟩ :=
    exists_uniform_allocated_original_mesh.{uG,uI,uB,uJ,uQ,uX} m dim
  obtain ⟨Kideal, hKideal, hselected⟩ :=
    exists_uniform_allocated_reference_prescribed_ideal.{uG,uI,uB,uJ,uQ,uX} m dim
  obtain ⟨Ksite, hKsite, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  refine ⟨A₀, T₀, Kproj, Kideal, Ksite, hA₀, hT₀, hKproj, hKideal, hKsite, ?_⟩
  intro G _ _ I _ n B _ p P E hp hP hE hdim hmP hpP hvars hI hn hBlocks
  unfold AllocatedUniformCommonCoverData
  intro D target w gainLog ε e eTail t
  let jets := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
  let rows := fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim))
  have hdimensions := allocatedComparisonDimensions_of_primitive B rows
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective) hp hvars hI hn
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    dsimp only [target, profileReferenceErrorLog]
    linarith
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hP
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdimensions.nonneg hP hw
  have he : 0 ≤ e := physicalIdealSmoothingLog_nonneg (layerSamplerDegree I n)
    A scalarSourceTransitionBound htarget hgain
  have heTail : 0 ≤ eTail := physicalIdealTailLog_nonneg G (G × Option (Fin dim))
    (layerSamplerDegree I n) A scalarSourceTransitionBound m htarget hgain
  obtain ⟨δ, hδ, hδ1, hδeq, hδe, ht, ht1, hselected⟩ :=
    hselected B ψ hψ hrange hzero hone A scalarSourceTransitionBound hLip
      scalarSourceTransitionBound_spec.2 hdimensions hP (show 0 ≤ E + 1 + 4 by linarith)
  have hsource : AllocatedOriginalPrescribedMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B D P (E + 1) e t δ A₀ T₀ Kproj Kideal :=
    horiginal B hdimensions hP (show 0 ≤ E + 1 by linarith) he ht1 hKideal hselected
  have hcommon : AllocatedCommonOriginalMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 1) e t δ A₀ T₀ Kproj Kideal :=
    allocatedOriginalPrescribedMeshAt_commonScale B hp hP (by linarith) hdim hmP hpP hvars hsource
  have hraw : AllocatedCommonResidueWeightedOriginalMeshAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P (E + 1) e t δ A₀ T₀ Kproj Kideal :=
    allocatedCommonOriginalMeshAt_residue_weighted B hcommon
  have hcover : AllocatedCommonRawCoverAt.{uG,uI,uB,uJ,uQ,uX}
      (G := G) (dim := dim) B p P E e t hP δ A₀ T₀ Kproj Kideal Ksite :=
    allocatedCommonRawCoverAt_of_source B hp hP hE he hdim hmP hpP hvars hI hn hBlocks
      hδ hδe hKsite (hSampling (fun j => fullBooleanRowSetFintype dim (j.val + 1))) hraw
  have htBound : t⁻¹ ≤ Real.exp eTail := by
    let : ∀ a : LayerSamplerAxis I n, Nonempty (jets a.1) := fun _ => ⟨⟨∅, by simp⟩⟩
    exact physicalIdeal_tail_inverse_le_exp G (G × Option (Fin dim))
      (layerSamplerDegree I n) (fun _ => Nat.succ_pos _) A scalarSourceTransitionBound m htarget hgain
  exact ⟨he, heTail, ht, ht1, htBound, δ, hδ, hδ1, hδeq, hδe, hcover,
    allocatedCommonRawCoverAt_genuine B hP hδ hδ1 hcover⟩

end Erdos3.VectorPolynomial

end

end OAI
