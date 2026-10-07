import OAI.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedInactiveGridSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

noncomputable def allocatedSupportedSlicedPhysicalJointPMF : PMF (∀ a, rows a → ℤ) :=
  (conditioned).toPMF.bind (fun y => dependentProductPMF (fun a =>
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2)))

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_law :
    allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x =
      dependentProductPMF (fun a => allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
        (selected a).1 (selected a).2 (rows a) x) := by
  let e (a : A) : LayerSamplerAxis I n := ⟨(selected a).1, Sum.inr (selected a).2⟩
  have he : Function.Injective e := by
    have hi : Function.Injective (fun z : (Σ j : Fin m, Fin (n j)) =>
        (⟨z.1, Sum.inr z.2⟩ : LayerSamplerAxis I n)) := by
      rintro ⟨j, i⟩ ⟨k, l⟩ h
      have hj : j = k := congrArg Sigma.fst h
      subst k
      have hsum : (Sum.inr i : I j ⊕ Fin (n j)) = Sum.inr l :=
        eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hl : i = l := Sum.inr.inj hsum
      subst l
      rfl
    exact hi.comp hselected
  let k (a : A) (y : ∀ b : B (e a), ∀ v : Fin (layerSamplerDegree I n (e a)),
      IntegerScalarCubeBox α (allocatedPrincipalSides B U basis S ⟨e a, b, v⟩)) : PMF (rows a → ℤ) :=
    (independentProductPMF (fun c : Option (B (e a)) =>
      allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2
        (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (e a) c))).map
      (fun c t => booleanCoefficient (fun _ : Finset α => c none) t +
        ∑ b, c (some b) * integerBooleanBlockJet (fun v i => (y b v i : ℤ)) t)
  have hpoint (a : A) (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α
      (allocatedPrincipalSides B U basis S)) :
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U basis S x y) ((selected a).1.val + 1)
        (fun t : rows a => (t : Finset α)))
        (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) =
      k a (fun b v => y ⟨e a, b, v⟩) := by
    exact allocatedPhysicalGridJetPMF_principal B U basis hR hσ S (selected a).1 (selected a).2
      (hgrid a) x y (fun t : rows a => (t : Finset α))
  unfold allocatedSupportedSlicedPhysicalJointPMF allocatedSupportedSlicedPhysicalGridPMF
  simp_rw [hpoint]
  exact containedSupportedProgressionLaw_selected_kernels B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell e he k

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_mass (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      ∏ a, (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
        (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  rw [allocatedSupportedSlicedPhysicalGrid_joint_law B U basis hR hσ S q r H step c hH hsubset hcell selected rows x
    hselected hgrid, dependentProductPMF_apply, ENNReal.toReal_prod]

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_scaled_mass (z : ∀ a, rows a → ℤ) :
    (∏ a, (basisAxisScale (basis (selected a).1) (selected a).2 : ℝ) ^ (rows a).card) *
      (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      ∏ a, (basisAxisScale (basis (selected a).1) (selected a).2 : ℝ) ^ (rows a).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
          (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  rw [allocatedSupportedSlicedPhysicalGrid_joint_mass B U basis hR hσ S q r H step c hH hsubset hcell selected rows x
    hselected hgrid, Finset.prod_mul_distrib]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uα

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j)) (rows : A → Finset (Finset α))

theorem allocatedSupportedSlicedJointGrid_site_approximation
    (hselected : Function.Injective selected)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (scale : A → ℕ) (e : A → ScalarSiteExpansion.{uα,uα} (Finset α))
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcap : ∀ a (x : G → IntegerScalarCubeBox α S.value) z,
      ‖((((scale a : ℝ) ^ (rows a).card) *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell (selected a).1 (selected a).2
          (rows a) x z).toReal : ℝ) : ℂ)‖ ≤ C)
    (he : ∀ a (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
      (∀ t ∉ rows a, booleanCoefficient y t = 0) →
      ‖((((scale a : ℝ) ^ (rows a).card) *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell (selected a).1 (selected a).2
          (rows a) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
        (e a).integerEval (scale a) y‖ ≤ uniformProductAccuracy (Fintype.card A) C δ) :
    ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
      (∀ a t, t ∉ rows a → booleanCoefficient (fun s => y s a) t = 0) →
      ‖((((∏ a, (scale a : ℝ) ^ (rows a).card)) *
        (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x
          (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
        siteFamilyEval e y (fun s a => (y s a : ℝ) / scale a)‖ ≤ δ := by
  intro x y hy
  let g (a : A) : ℂ := ((scale a : ℝ) ^ (rows a).card *
    (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell (selected a).1 (selected a).2
      (rows a) x (fun t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ)
  have hprod := siteFamily_approximation e y (fun s a => (y s a : ℝ) / scale a) g
    (Fintype.card A) le_rfl hC hδ (fun a => hcap a x _) (fun a => he a x _ (hy a))
  have heq : ((((∏ a, (scale a : ℝ) ^ (rows a).card)) *
      (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x
        (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) = ∏ a, g a := by
    rw [allocatedSupportedSlicedPhysicalGrid_joint_mass B U basis hR hσ S q r H step c hH hsubset hcell
      selected rows x hselected hgrid _, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  rw [heq]
  exact hprod

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell grid

omit [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedPhysicalGridJetPMF_restrict_join (j : Fin m) (i : Fin (n j))
    (hgrid : grid ⟨j, Sum.inr i⟩)
    (row : Finset (Finset α))
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) (fun t : row => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid (principalAxisRestrict grid y) v₀))
      (j.val + 1) (fun t : row => (t : Finset α))) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) := by
  rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x y,
    allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x (principalAxisJoin grid (principalAxisRestrict grid y) v₀)]
  congr 1
  funext c t
  simp only [principalAxisJoin, principalAxisRestrict, hgrid, ↓reduceDIte]

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_marginal
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)) :
    allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x =
      (gridLaw).toPMF.bind (fun u => dependentProductPMF (fun a =>
        integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))) := by
  let k (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S)) : PMF (∀ a, rows a → ℤ) :=
    dependentProductPMF (fun a => integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
      (fun t : rows a => (t : Finset α)))
      (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2))
  have hm := congrArg (fun p => p.bind k)
    (containedSupportedProgressionLaw_axis_marginal B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
      hH hsubset q r hcell grid)
  rw [PMF.bind_map] at hm
  refine Eq.trans ?_ hm
  apply congrArg (conditioned).toPMF.bind
  funext y
  apply congrArg dependentProductPMF
  funext a
  exact allocatedPhysicalGridJetPMF_restrict_join B U basis hR hσ S x (selected a).1 (selected a).2
    (hgrid a) (rows a) y v₀

theorem allocatedSupportedSlicedPhysicalJointPMF_grid_mean
    (hgrid : ∀ a, grid ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U basis S))
    (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      (gridLaw).mean (fun u => ∏ a,
        (integerMatrixImagePMF (boundedCoefficientJetMatrix
          (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v₀))
          (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v₀)) ((selected a).1.val + 1)
          (fun t : rows a => (t : Finset α)))
          (allocatedLayerIntegerPMFs B U basis hR hσ S (selected a).1 (selected a).2) (z a)).toReal) := by
  rw [allocatedSupportedSlicedPhysicalJointPMF_grid_marginal B U basis hR hσ S q r H step c hH hsubset hcell
    selected rows x hgrid v₀, FiniteProbabilityWeights.toPMF_bind_toReal]
  apply congrArg (gridLaw).mean
  funext u
  rw [dependentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3.VectorPolynomial

end

end OAI
