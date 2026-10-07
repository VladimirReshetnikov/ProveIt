import OAI.Combinatorics.Progressions.Linear.RankPreparationPaddedFreezingLifts

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

include hmq in
omit [Fintype X] [∀ j, Fintype (Deck j)] in

theorem exists_freeze_allocated_padded_recovered_sample
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (a : X → ℤ) (v : Option Vars × X → ℤ)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c a v sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (parentDomain : Set (X → ℤ))
    (herr : ∀ x ∈ parentDomain, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hbudget : (D : ℝ) * (2 * ((∑ j, (Fintype.card (L.pad q j).Coord : ℝ) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ)) < 1 / 12)
    (hscoreBudget : A.kernel.lip * ((D : ℝ) * (2 *
      ((∑ j, (Fintype.card (L.pad q j).Coord : ℝ) *
        (C j * (((Fintype.card (I j) : ℝ) + 1) * R j))) + δ))) ≤ gain / 16)
    {Ω : Type} [Fintype Ω] (t : Ω → Vars → ℤ)
    (hbox : ∀ u k, |(t u k : ℝ)| ≤ layerSamplerBox B U b S k)
    (hinside : ∀ u, integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
      (jointIntegerFrame (a,v) none) (t u) ∈ parentDomain)
    (score : Ω → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (a,v) (some k) x)
        (jointIntegerFrame (a,v) none) (t u) x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (t u k : ℝ)) := by
  let frame := jointIntegerFrame (a,v)
  let point : Ω → X → ℝ := fun u x =>
    (frame none x : ℝ) + ∑ k, (frame (some k) x : ℝ) * (t u k : ℝ)
  have hscore' : gain / 2 ≤ 𝔼 u, score u * A.value (point u) := by
    simpa only [point, frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using hscore
  obtain ⟨β, hβ, _, hsmall⟩ := hread.freezing_lifts B U b hb o S hR hσ
    (fun j => (L.pad q j).poly) hm hσ1 C hC hchart hp c a v sample read
  let ε : Fin q → ℝ := fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * R j)
  have hε : ∀ j, 0 ≤ ε j := by
    intro j
    exact mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  let domain : Set (Vars → ℝ) := Set.range (fun u k => (t u k : ℝ))
  obtain ⟨u₀, bref, href⟩ := A.exists_contributing_site_of_pos_score point score
    ((half_pos hgain).trans_le hscore')
  let : Nonempty Ω := ⟨u₀⟩
  let βold := L.unpadFreezingLifts hmq β
  have hβold : ∀ j i, (βold j i).totalDegree ≤ j.val + 1 :=
    L.unpadFreezingLifts_degree hmq β hβ
  let εold := fun j : Fin m => ε (j.castLE hmq)
  have hsum : (∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * εold j) =
      ∑ j : Fin q, (Fintype.card (L.pad q j).Coord : ℝ) * ε j :=
    L.pad_coordinateWeighted_sum hmq ε
  have hbudgetOld : (D : ℝ) * (2 *
      ((∑ j : Fin m, (Fintype.card (L j).Coord : ℝ) * εold j) + δ)) < 1 / 12 := by
    rw [hsum]
    exact hbudget
  have hsmallOld := L.unpadFreezingLifts_bound hmq β (fun j => (c j).val)
    (fun x v => (frame none v : ℝ) + ∑ k, (frame (some k) v : ℝ) * x k)
    domain ε (by
      rintro x ⟨u, rfl⟩
      exact hsmall _ (hbox u))
  obtain ⟨A', hLip, hweight, hclose⟩ := F.exists_freeze_prepared_affine L ip hip c₀ err
    hprepare frame βold hβold (L.unpadCenter hmq (fun j => (c j).val))
    εold (fun j => hε _) hδ domain
    (by rintro x ⟨u, rfl⟩; exact ⟨t u, rfl⟩)
    hsmallOld
    (by
      rintro x ⟨u, rfl⟩ i
      simpa only [frame, integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul] using
        herr _ (hinside u) i)
    (fun k => (t u₀ k : ℝ)) ⟨u₀, rfl⟩ bref href hbudgetOld
  rw [hsum] at hclose
  refine ⟨A', hLip, hweight, ?_⟩
  have hcompare : (𝔼 u, score u * A.value (point u)) ≤
      (𝔼 u, score u * A'.value (fun k => (t u k : ℝ))) + gain / 16 := by
    calc
      _ ≤ 𝔼 u, (score u * A'.value (fun k => (t u k : ℝ)) + gain / 16) := by
        apply Finset.expect_le_expect
        intro u _
        exact unit_weight_score_error (hscoreBound u)
          ((hclose _ ⟨u, rfl⟩).trans hscoreBudget)
      _ = _ := by rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  linarith

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
