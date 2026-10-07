import OAI.Combinatorics.Progressions.Dynamics.PreparedBadProductInputBudget
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uα
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformEarlyRadius (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {p g : ℝ}, 0 ≤ p → 0 ≤ g →
      let pRadius := allocatedCommonProductRadiusLog m p g
      let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
      pRadius ∈ Set.Icc 0 ((p + g + A) ^ A) ∧
      (∀ j, 0 < R j ∧ R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      ∀ {G : Type uG} [Fintype G] {I : Fin m → Type uI} [∀ j, Fintype (I j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
        {α : Type uα} [Fintype α] (rowSets : Fin m → Finset (Finset α))
        [∀ j, Nonempty (rowSets j)],
        Fintype.card α ≤ m + 1 →
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
  obtain ⟨A, hA, hbound⟩ := exists_allocatedCommonProductRadiusLog_bound m
  refine ⟨A, hA, ?_⟩
  intro p g hp hg pRadius R
  obtain ⟨hlog, hpos, hone, hinv, _⟩ := allocatedCommonProductRadius_bounds m hp hg
  refine ⟨⟨hlog, hbound hp hg⟩, fun _ => ⟨hpos, hone, hinv.le⟩, ?_⟩
  intro G _ I _ n B _ α _ rowSets _ hdim hvars hI hn
  dsimp only
  have hgeo := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    (fun _ => 0) (fun _ => le_refl 0) (fun _ => Real.exp_nonneg g)
    (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeo.2.2.2.1, hgeo.2.2.2.2.1, ?_⟩
  intro C hC hCg
  have hgeometry := allocatedCanonicalSlice_source_geometry B rowSets hp hg hdim hvars hI hn
    C hC hCg (fun _ => hpos.le) (fun _ => le_refl (allocatedCommonProductRadius m p g))
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

section

namespace Erdos3

theorem twice_chartCoefficient_le_exp {C Pchart Bstruct : ℝ}
    (hC : C ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ Bstruct) :
    2 * C ≤ Real.exp Bstruct := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.add_one_le_exp (1 : ℝ)]
  calc
    2 * C ≤ 2 * Real.exp Pchart := mul_le_mul_of_nonneg_left hC (by norm_num)
    _ ≤ Real.exp 1 * Real.exp Pchart :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (Pchart + 1) := by rw [← Real.exp_add, add_comm]
    _ ≤ Real.exp Bstruct := Real.exp_le_exp.mpr hallow

namespace VectorPolynomial

theorem preparedEarlyRadius_eighth_of_universal
    {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)]
    {R : Fin m → ℝ} {Pchart Bstruct : ℝ}
    (hbudget : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Bstruct) →
      ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j, C j ≤ Real.exp Pchart)
    (hallow : Pchart + 1 ≤ Bstruct) :
    ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 8 := by
  have hdoubled := hbudget (fun j => 2 * C j)
    (fun j => mul_nonneg (by norm_num) (hC j))
    (fun j => twice_chartCoefficient_le_exp (hchart j) hallow)
  intro j
  nlinarith only [hdoubled j]

theorem preparedUniformEarlyRadius_eighth
    {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
    [∀ j, Nonempty (rowSets j)] {p g Pchart : ℝ}
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hdim : Fintype.card α ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j, C j ≤ Real.exp Pchart) (hallow : Pchart + 1 ≤ g) :
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m p g
    let T := allocatedIdealCoverSupport (G := G) B rowSets
    let r := allocatedProductIdealSiteRadius (G := G) B rowSets
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 8) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 8) ∧
      (∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 8) := by
  intro R T r
  obtain ⟨_, _, hfamilies⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius m)).2 hp hg
  have hgeometry := hfamilies (G := G) B rowSets hdim hvars hI hn
  have hsmall := hgeometry.2.2.2.2.2
  have hdoubled := hsmall (fun j => 2 * C j)
    (fun j => mul_nonneg (by norm_num) (hC j))
    (fun j => twice_chartCoefficient_le_exp (hchart j) hallow)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    nlinarith only [hdoubled.1 j]
  · intro j
    nlinarith only [hdoubled.2.1 j]
  · intro j
    nlinarith only [hdoubled.2.2 j]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

theorem preparedBadProduct_dimension_le_initial_allocation (m d : ℕ) :
    d ≤ modularInitialBlockCount m d := by
  have hp : 0 < (2 : ℕ) ^ m := by positivity
  unfold modularInitialBlockCount
  nlinarith [Nat.zero_le (modularInitialRankStrength m d)]

theorem preparedBadProduct_witness_count_le_dimension_sq (m nX M : ℕ) :
    modularInitialBlockCount m (nX + m * M) * (nX + m * M) ≤
      enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M)) ^ 2 := by
  have halloc := enlargedPreparedCommonSamplerDimension_allocation m M
    (modularInitialBlockCount m (nX + m * M))
  have hdim := (preparedBadProduct_dimension_le_initial_allocation m (nX + m * M)).trans halloc
  simpa only [pow_two] using Nat.mul_le_mul halloc hdim

theorem preparedBadProductWitnessGap_bounds (m nX M : ℕ) {P0 Elog Vlog : ℝ}
    (hpnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ P0)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let W := physicalBadProductGap (modularInitialBlockCount m (nX + m * M) * (nX + m * M))
      Elog Vlog Q
    1 ≤ W ∧ W ≤ Real.exp (2 * P0 + 2 * Vlog + 5 * Elog + 24) := by
  intro W
  have hP0 : 0 ≤ P0 := (Nat.cast_nonneg _).trans hpnum
  have hN : ((modularInitialBlockCount m (nX + m * M) * (nX + m * M) : ℕ) : ℝ) ≤
      Real.exp (2 * P0) := by
    have hnum : (enlargedPreparedCommonSamplerDimension m M
        (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Real.exp P0 :=
      hpnum.trans (by linarith [Real.add_one_le_exp P0])
    calc
      _ ≤ (enlargedPreparedCommonSamplerDimension m M
          (modularInitialBlockCount m (nX + m * M)) : ℝ) ^ 2 := by
        exact_mod_cast preparedBadProduct_witness_count_le_dimension_sq m nX M
      _ ≤ (Real.exp P0) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnum 2
      _ = Real.exp (2 * P0) := by rw [two_mul, Real.exp_add, pow_two]
  exact ⟨(physicalBadProductGap_budget _ hElog hVlog Q hQ hQexp).1,
    physicalBadProductGap_exp_bound _ hElog hVlog (by positivity) Q hQexp hN⟩

section Source
variable {X₀ J₀ : Type} {m : ℕ} (prep : RankPreparationFamily X₀ J₀ m) (nX M : ℕ)
local notation "Jalloc" => modularInitialBlockCount m (nX + m * M)
local notation "Kernel" => EnlargedPreparedCommonKernel m Jalloc
local notation "Cont" => PreparedSamplerContinuous prep
local notation "Trans" => preparedSamplerTransverse prep
local notation "Blocks" => EnlargedPreparedCommonSamplerBlock prep Jalloc

theorem exists_preparedBadProductWitnessScale
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Basis (Fin (Trans j)) ℝ (euclideanSubspace (U j))ᗮ)
    (R σ : Fin m → ℝ)
    (S0 : LayerSamplerScale (G := Kernel) (I := Cont) (n := Trans) (J := J) Blocks U basis R σ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P0 Elog Vlog : ℝ}
    (hdim : AllocatedComparisonDimensions (G := Kernel) (I := Cont) (n := Trans) Blocks α O D)
    (hDP : D ≤ P0) (hpnum : (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ P0)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P0) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P0)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P0)
    (hElog : 0 ≤ Elog) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let W := physicalBadProductGap (Jalloc * (nX + m * M)) Elog Vlog Q
    1 ≤ W ∧ W ≤ Real.exp (2 * P0 + 2 * Vlog + 5 * Elog + 24) ∧
    ∃ S : LayerSamplerScale (G := Kernel) (I := Cont) (n := Trans) (J := J) Blocks U basis R σ,
      S0.value ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog P0 (2 * P0 + 2 * Vlog + 5 * Elog + 24)) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := Kernel) (I := Cont) (n := Trans) Blocks R ⟨j, i⟩ / 2) *
            ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  intro W
  have hP0 : 0 ≤ P0 := hdim.nonneg.trans hDP
  obtain ⟨hW, hWexp⟩ := preparedBadProductWitnessGap_bounds m nX M hpnum hElog hVlog Q hQ hQexp
  refine ⟨hW, hWexp, ?_⟩
  exact exists_allocatedWitnessScale_of_bounded_source (G := Kernel) (I := Cont) (n := Trans)
    Blocks U basis R σ S0 hdim hDP hR hσ hRi hσi hS0 hW (by positivity) hWexp

end Source
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedFiniteCanonicalSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension m M
      (modularInitialBlockCount m (nX + m * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel m
      (modularInitialBlockCount m (nX + m * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ)
        ≤ Bstruct ∧ (m : ℝ) ≤ Bstruct := by
  let Jalloc := modularInitialBlockCount m (nX + m * M)
  have hcounts := preparedBadProduct_input_counts prep Jalloc nX hCoord
  have htags : Fintype.card (Fin nX ⊕ (Σ j, (prep j).Coord)) ≤ nX + m * M := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
    apply Nat.add_le_add_left
    calc
      ∑ j : Fin m, Fintype.card (prep j).Coord ≤ ∑ _j : Fin m, M :=
        Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have htagsDimension := htags.trans
    ((preparedBadProduct_dimension_le_initial_allocation m (nX + m * M)).trans
      (enlargedPreparedCommonSamplerDimension_allocation m M Jalloc))
  exact ⟨(Nat.cast_le.mpr hcounts.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr htagsDimension).trans hnum,
    (Nat.cast_le.mpr hcounts.2.2.2.2.1).trans hnum,
    (Nat.cast_le.mpr hcounts.1).trans hnum⟩

theorem preparedFiniteNestedSource_counts
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct) :
    (Fintype.card (EnlargedPreparedCommonKernel (max m cutoff)
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M))) : ℝ) ≤ Bstruct ∧
    (Fintype.card (Fin nX ⊕ (Σ j, (prep.pad (max m cutoff) j).Coord)) : ℝ) ≤ Bstruct ∧
    (Fintype.card (LayerSamplerVariables
      (EnlargedPreparedCommonKernel (max m cutoff)
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))
      (PreparedSamplerContinuous (prep.pad (max m cutoff)))
      (preparedSamplerTransverse (prep.pad (max m cutoff)))
      (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff))
        (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)))) : ℝ)
        ≤ Bstruct ∧ ((max m cutoff : ℕ) : ℝ) ≤ Bstruct :=
  preparedFiniteCanonicalSource_counts (prep.pad (max m cutoff)) nX M
    (prep.pad_coordinate_card_le hCoord) hnum

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators

theorem preparedFiniteNestedSource_relative_radius
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff : ℕ) {Bstruct Pearly : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct)
    (hEarly : Pearly ≤ Bstruct) :
    ∀ C : Fin (max m cutoff) → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pearly) → ∀ j,
      C j * ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m cutoff)) j) : ℝ) + 1) *
        allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct ≤ 1 / 4 := by
  let q := max m cutoff
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let rows : Fin q → Finset (Finset (Fin 0)) := fun _ => {∅}
  let _ : ∀ j, Nonempty (rows j) := fun _ => ⟨⟨∅, by simp [rows]⟩⟩
  obtain ⟨_, _, hvariables, _⟩ := preparedFiniteNestedSource_counts prep nX M cutoff hCoord hnum
  obtain ⟨_, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions
    (prep.pad q) Jalloc (prep.pad_coordinate_card_le hCoord)
  obtain ⟨_, _, hfam⟩ := (Classical.choose_spec (exists_preparedUniformEarlyRadius q)).2 hB hB
  have hgeo := hfam (G := EnlargedPreparedCommonKernel q Jalloc)
    (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc) rows
    (by simp) hvariables
    (fun j => (Nat.cast_le.mpr (hI j)).trans hnum)
    (fun j => (Nat.cast_le.mpr (hn j)).trans hnum)
  intro C hC hCB
  exact (hgeo.2.2.2.2.2 C hC
    (fun j => (hCB j).trans (Real.exp_le_exp.mpr hEarly))).1

noncomputable def preparedNestedRelativeCommonFloor
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    (x relativeCutoff : ℝ) : ℕ :=
  max (preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x)
    (Nat.ceil (Real.exp (max 0 relativeCutoff)))

noncomputable def preparedNestedRelativeCommonFloorLog
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    (x relativeCutoff : ℝ) : ℝ :=
  max (candidateNestedForwardSeed A constants innerDepth outerDepth x + 1)
    (max 0 relativeCutoff + 1)

theorem preparedNestedRelativeCommonFloor_bounds
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    {x : ℝ} (hx : 0 ≤ x) (relativeCutoff : ℝ) :
    0 ≤ preparedNestedRelativeCommonFloorLog A constants innerDepth outerDepth x relativeCutoff ∧
    (preparedNestedRelativeCommonFloor A constants innerDepth outerDepth x relativeCutoff : ℝ) ≤
      Real.exp (preparedNestedRelativeCommonFloorLog A constants innerDepth outerDepth x relativeCutoff) ∧
    preparedNestedScalarAnchorFloor A constants innerDepth outerDepth x ≤
      preparedNestedRelativeCommonFloor A constants innerDepth outerDepth x relativeCutoff ∧
    Nat.ceil (Real.exp (max 0 relativeCutoff)) ≤
      preparedNestedRelativeCommonFloor A constants innerDepth outerDepth x relativeCutoff ∧
    Real.exp relativeCutoff ≤ (Nat.ceil (Real.exp (max 0 relativeCutoff)) : ℝ) ∧
    (Nat.ceil (Real.exp (max 0 relativeCutoff)) : ℝ) ≤ Real.exp (max 0 relativeCutoff + 1) := by
  have ha := (preparedNestedScalarAnchorFloor_bounds A constants innerDepth outerDepth hx).2
  have hr := ceil_exp_le_exp_add_one (le_max_left (0 : ℝ) relativeCutoff)
  refine ⟨?_, ?_, le_max_left _ _, le_max_right _ _, ?_, hr⟩
  · exact (by positivity : (0 : ℝ) ≤ max 0 relativeCutoff + 1).trans (le_max_right _ _)
  · rw [preparedNestedRelativeCommonFloor, Nat.cast_max]
    exact max_le
      (ha.trans (Real.exp_le_exp.mpr (le_max_left _ _)))
      (hr.trans (Real.exp_le_exp.mpr (le_max_right _ _)))
  · exact (Real.exp_le_exp.mpr (le_max_right _ _)).trans (Nat.le_ceil _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedNestedRelativeCommonFloorLog_power_budget
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth inputPower : ℕ)
    (hA : 2 ≤ A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x relativeCutoff : ℝ}, 0 ≤ x →
      relativeCutoff ≤ (x + 2) ^ inputPower →
      preparedNestedRelativeCommonFloorLog A constants innerDepth outerDepth x relativeCutoff ≤
        (x + 2) ^ C := by
  obtain ⟨D, _, hseedBound⟩ := exists_candidateNestedForwardSeed_polynomial_budget
    A constants innerDepth outerDepth (Polynomial.X + 1)
  let P : Polynomial ℕ := (Polynomial.X + 2) ^ D +
    (Polynomial.X + 2) ^ inputPower + 1
  obtain ⟨C, hC, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro x relativeCutoff hx hcutoff
  have hseed : candidateNestedForwardSeed A constants innerDepth outerDepth x + 1 ≤
      (x + 2) ^ D := by
    simpa using hseedBound hx outerDepth le_rfl
  have hseedNonneg : 0 ≤ candidateNestedForwardSeed A constants innerDepth outerDepth x + 1 := by
    have h := hx.trans (le_candidateNestedForwardSeed A constants innerDepth outerDepth hA hx)
    linarith only [h]
  have hinputNonneg : 0 ≤ (x + 2) ^ inputPower := by positivity
  have hcutoff' : max 0 relativeCutoff ≤ (x + 2) ^ inputPower :=
    max_le hinputNonneg hcutoff
  calc
    preparedNestedRelativeCommonFloorLog A constants innerDepth outerDepth x relativeCutoff ≤
        (candidateNestedForwardSeed A constants innerDepth outerDepth x + 1) +
          (max 0 relativeCutoff + 1) := by
      unfold preparedNestedRelativeCommonFloorLog
      exact max_le (le_add_of_nonneg_right (by positivity))
        (le_add_of_nonneg_left hseedNonneg)
    _ ≤ (x + 2) ^ D + (x + 2) ^ inputPower + 1 := by
      linarith only [hseed, hcutoff']
    _ ≤ (x + 2) ^ C := by
      simpa [P, Polynomial.eval₂_pow] using hP x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

theorem preparedFiniteNestedSource_relative_initializer_bounds
    {m : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    (nX M cutoff A innerDepth outerDepth : ℕ) (constants : ℕ → ℕ)
    {Slot : Type*} [Fintype Slot]
    {Bstruct gainLog pRelative relativeCutoff anchorRequired conditionalRequired : ℝ}
    (detectorRequired : Slot → ℝ) (N : Fin nX → ℕ) (Svalue : ℕ)
    (hA : 2 ≤ A) (hcutoff : 1 ≤ cutoff)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hg : 0 ≤ gainLog) (hgB : gainLog ≤ Bstruct)
    (hnX : (nX : ℝ) ≤ Bstruct)
    (hnum : (enlargedPreparedCommonSamplerDimension (max m cutoff) M
      (modularInitialBlockCount (max m cutoff) (nX + max m cutoff * M)) : ℝ) ≤ Bstruct)
    (hrelative : 6 * pRelative + 35 ≤ Bstruct)
    (hN : ∀ i, Real.exp (preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      Bstruct anchorRequired conditionalRequired detectorRequired) ≤ (N i : ℝ))
    (hS : preparedNestedRelativeCommonFloor A constants innerDepth outerDepth
      Bstruct relativeCutoff ≤ Svalue) :
    let τ := Real.exp (-(gainLog + nX + 8))
    let H := Nat.ceil (Real.exp (max 0 relativeCutoff))
    τ ≤ 1 / 2 ∧ (∀ i, 4 ≤ τ * (N i : ℝ)) ∧ H ≤ Svalue ∧
      Real.exp relativeCutoff ≤ (H : ℝ) ∧
      ∀ C : Fin (max m cutoff) → ℝ, (∀ j, 0 ≤ C j) →
        (∀ j, C j ≤ Real.exp (6 * pRelative + 35)) → ∀ j,
        C j * ((Fintype.card (PreparedSamplerContinuous (prep.pad (max m cutoff)) j) : ℝ) + 1) *
          allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct ≤ 1 / 4 := by
  intro τ H
  have htrim := preparedFiniteNestedSourceRequired_trim_bounds A constants innerDepth outerDepth
    cutoff Bstruct anchorRequired conditionalRequired detectorRequired nX N
    hA hcutoff hB hgB hnX hg hN
  have hfloor := preparedNestedRelativeCommonFloor_bounds A constants innerDepth outerDepth
    hB relativeCutoff
  exact ⟨htrim.2.1, htrim.2.2.2, hfloor.2.2.2.1.trans hS, hfloor.2.2.2.2.1,
    preparedFiniteNestedSource_relative_radius prep nX M cutoff hCoord hB hnum hrelative⟩

end Erdos3.VectorPolynomial

end

end OAI
