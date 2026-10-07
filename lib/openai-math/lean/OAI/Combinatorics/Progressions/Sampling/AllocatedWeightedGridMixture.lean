import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
import OAI.Combinatorics.Progressions.Estimates.IndependentPMFOption

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedLayerInteger_moderate_jet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : LayerSamplerVariables G I n B → Option α → ℤ)
    (rows : O → Finset α) (o : O) :
    (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * x v r) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) r) (rows o) := by
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval
      (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) = _
  have he (t : Finset α) := allocatedLayerInteger_moderate_eval B U basis hR hσ S j i
    hmoderate a ha (fun v => ∑ r, (booleanFeature r t : ℤ) * x v r)
  simp_rw [he, booleanCoefficient_add, booleanCoefficient_sum, booleanCoefficient_const_mul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJet_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) (o : O) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows *ᵥ a) o =
      booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
        ∑ b : B ⟨j, Sum.inr i⟩,
          a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o) := by
  let tuple : LayerSamplerVariables G I n B → Option α → ℤ := fun v r =>
    Sum.elim (fun g => (x g r : ℤ)) (fun q => (y q r : ℤ)) v
  have hvert : integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) =
      (fun t v => ∑ r, (booleanFeature r t : ℤ) * tuple v r) := by
    funext t v
    rw [allocatedPhysicalCube_vertex]
    cases v <;> simp [tuple, integerScalarCubeValue, Fintype.sum_option, booleanFeature, ite_mul]
  change (integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ))
    (integerAffineCube (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) rows *ᵥ a) o = _
  rw [hvert]
  exact allocatedLayerInteger_moderate_jet_blocks B U basis hR hσ S j i hmoderate a ha tuple rows o

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJetPMF_blocks
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
        (fun a o => booleanCoefficient (fun _ => a (constantCoefficientSlot _ _)) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩,
            a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
              integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  unfold integerMatrixImagePMF
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases ha : independentProductPMF (allocatedLayerIntegerPMFs B U basis hR hσ S j i) a = 0
  · simp only [ha, ite_self]
  · have hs : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support := by
      intro d
      change allocatedLayerIntegerPMFs B U basis hR hσ S j i d (a d) ≠ 0
      rw [independentProductPMF_apply] at ha
      exact (Finset.prod_ne_zero_iff.mp ha) d (Finset.mem_univ d)
    have he := funext (fun o => allocatedPhysicalGridJet_blocks B U basis hR hσ S j i
      hmoderate a hs x y rows o)
    rw [he]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) ((j : ℕ) + 1)

theorem allocatedPhysicalGridJetPMF_principal
    (hmoderate : basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1))
    {α O : Type*} [Fintype α] [DecidableEq α]
    (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (rows : O → Finset α) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) (j.val + 1) rows)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (independentProductPMF (fun r : Option (B ⟨j, Sum.inr i⟩) =>
        allocatedLayerIntegerPMFs B U basis hR hσ S j i
          (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ r))).map
        (fun c o => booleanCoefficient (fun _ => c none) (rows o) +
          ∑ b : B ⟨j, Sum.inr i⟩, c (some b) *
            integerBooleanBlockJet (fun v r => (y ⟨⟨j, Sum.inr i⟩, b, v⟩ r : ℤ)) (rows o)) := by
  rw [allocatedPhysicalGridJetPMF_blocks B U basis hR hσ S j i hmoderate x y rows]
  rw [← principalCoefficientMarginal (G := G) (B := B) (layerSamplerDegree I n)
    ⟨j, Sum.inr i⟩ (Nat.zero_lt_succ _) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)]
  rw [PMF.map_comp]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α O : Type*} [Fintype α] [DecidableEq α] (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "frozen" => allocatedFrozenTupleWeights (α := α) B U basis S
local notation "principalLaw" => independentProductPMF
  (fun r : Option (B (Sigma.mk j (Sum.inr i))) => allocatedLayerIntegerPMFs B U basis hR hσ S j i
    (principalCoefficientChoice (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) r))

noncomputable def allocatedFrozenPrincipalJet
    (c : Option (B ⟨j, Sum.inr i⟩) → ℤ)
    (u : PrincipalAxisTuples (α := α) grid sides) : O → ℤ :=
  fun o => booleanCoefficient (fun _ => c none) (rows o) +
    ∑ b : B ⟨j, Sum.inr i⟩, c (some b) *
      integerBooleanBlockJet (fun v r => (u ⟨⟨⟨j, Sum.inr i⟩, hgrid⟩, b, v⟩ r : ℤ)) (rows o)

theorem allocatedFrozenGrid_marked_principal_mixture
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    (frozen).toPMF.bind (fun u =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
          (fun z => (u, z))) =
      (principalLaw).bind (fun c => (frozen).toPMF.map
        (fun u => (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u))) := by
  have hpoint (u : PrincipalAxisTuples (α := α) grid sides) :
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (principalLaw).map (fun c => allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x
      (principalAxisJoin grid u v) rows]
    congr 1
    funext c o
    simp only [allocatedFrozenPrincipalJet, principalAxisJoin, hgrid, ↓reduceDIte]
  simp_rw [hpoint, PMF.map_comp]
  exact PMF.bind_comm _ _ (fun u c =>
    PMF.pure (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u))

theorem allocatedFrozenGrid_separated_principal_mixture
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    (frozen).toPMF.bind (fun u =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
          (fun z => (u, z))) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun c => (independentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
          allocatedLayerIntegerPMFs B U basis hR hσ S j i
            (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ (some b)))).bind
          (fun a => (frozen).toPMF.map (fun u =>
            (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows
              (fun r => r.elim c a) u)))) := by
  rw [allocatedFrozenGrid_marked_principal_mixture B U basis hR hσ S j i hgrid rows x v,
    independentProductPMF_option, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
variable {α O : Type*} [Fintype α] [DecidableEq α] (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "principalLaw" => independentProductPMF
  (fun r : Option (B (Sigma.mk j (Sum.inr i))) => allocatedLayerIntegerPMFs B U basis hR hσ S j i
    (principalCoefficientChoice (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) r))

theorem allocatedGrid_marked_principal_mixture_of_law
    (law : PMF (PrincipalAxisTuples (α := α) grid sides))
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    law.bind (fun u =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
          (fun z => (u, z))) =
      (principalLaw).bind (fun c => law.map
        (fun u => (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u))) := by
  let _ : ∀ index, DecidableEq (I index) := inferInstance
  let _ : ∀ axis, DecidableEq (B axis) := inferInstance
  have hpoint (u : PrincipalAxisTuples (α := α) grid sides) :
      integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i) =
      (principalLaw).map (fun c => allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u) := by
    rw [allocatedPhysicalGridJetPMF_principal B U basis hR hσ S j i hgrid x
      (principalAxisJoin grid u v) rows]
    congr 1
    funext c o
    simp only [allocatedFrozenPrincipalJet, principalAxisJoin, hgrid, ↓reduceDIte]
  simp_rw [hpoint, PMF.map_comp]
  exact PMF.bind_comm _ _ (fun u c =>
    PMF.pure (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows c u))

theorem allocatedGrid_separated_principal_mixture_of_law
    (law : PMF (PrincipalAxisTuples (α := α) grid sides))
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    law.bind (fun u =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix
        (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u v))
        (j.val + 1) rows) (allocatedLayerIntegerPMFs B U basis hR hσ S j i)).map
          (fun z => (u, z))) =
      (allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ none)).bind
        (fun c => (independentProductPMF (fun b : B ⟨j, Sum.inr i⟩ =>
          allocatedLayerIntegerPMFs B U basis hR hσ S j i
            (principalCoefficientChoice (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ (some b)))).bind
          (fun a => law.map (fun u =>
            (u, allocatedFrozenPrincipalJet B U basis S j i hgrid rows
              (fun r => r.elim c a) u)))) := by
  rw [allocatedGrid_marked_principal_mixture_of_law B U basis hR hσ S j i hgrid rows law x v,
    independentProductPMF_option, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

end Erdos3.VectorPolynomial

end

end OAI
