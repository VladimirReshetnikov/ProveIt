import OAI.Combinatorics.Progressions.Estimates.AllocatedWindowPrefactor

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} (d : ℕ)
variable (x : G → IntegerScalarCubeBox α S.value) (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell

variable (T : Fin m → ℝ)
variable (hTi : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hTw : ∀ j i, allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩ + 1 ≤ T j)

include hTi hTw in
theorem allocatedWindowMixed_coordinate_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (z : MixedCoveredJetSource I O E n d)
    (hw : allocatedActiveWindowCondition B U b S rowSets d z)
    (hi : (∏ a : {a : {a // grid a} // ¬active a}, (laws a.val ((split z.1).1 a.val)).toReal) ≠ 0)
    (hl : ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |allocatedLongJetRealCoordinates B U b S ((split z.1).2) ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (j : Fin m) (t : O j) :
    (∀ i, |(z.1 j).1 i t| ≤ T j * R j) ∧
      (∀ i, |((z.1 j).2 i t : ℝ) / basisAxisScale (b j) i| ≤ T j * R j) := by
  constructor
  · intro i
    exact hl ⟨⟨j, Sum.inl i⟩, by change ¬False; exact not_false⟩ t
  · intro i
    by_cases hg : grid ⟨j, Sum.inr i⟩
    · let a : {a // grid a} := ⟨⟨j, Sum.inr i⟩, hg⟩
      by_cases ha : active a
      · have hwn := hw ⟨a, ha⟩
        change (z.1 j).2 i ∈ naturalScaleIntegerWindow (rowSets j)
          (allocatedSiteCoefficientRadius (G := G) B rowSets ⟨j, i⟩)
          (allocatedPrincipalGridScale (G := G) B U b (R := R) j i) at hwn
        exact (allocatedActiveWindow_scaled_bound B U b hR S rowSets j i ha _ hwn t).trans
          (mul_le_mul_of_nonneg_right (hTw j i) (hR j).le)
      · have hp : (laws a ((split z.1).1 a)).toReal ≠ 0 := by
          intro hzero
          exact hi (Finset.prod_eq_zero (Finset.mem_univ ⟨a, ha⟩) hzero)
        exact (allocatedSupportedGridJetPMF_scaled_support_bound B U b hR hσ S x rows q
          (principalResidueLabel q y₀) hcell j (hσ1 j) i hg ((z.1 j).2 i) hp t).trans
          (mul_le_mul_of_nonneg_right (hTi j) (hR j).le)
    · exact hl ⟨⟨j, Sum.inr i⟩, hg⟩ t

variable [∀ j, Fintype (E j)] [NeZero d]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

include hTi hTw in
theorem allocatedActiveWindowPrefactor_sites_quarter
    (hT : ∀ j, 0 ≤ T j) (hσ1 : ∀ j, σ j ≤ 1)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, (rowSets j).card * (C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j))) ≤ 1 / 4)
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)))
    (hne : allocatedActiveWindowPrefactor B U b S rowSets d hR hσ x hb o bW q y₀ hcell f z ≠ 0)
    (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j)) := by
  obtain ⟨hw, hi, hl⟩ := allocatedActiveWindowPrefactor_support B U b S rowSets d hR hσ
    x hb o bW q y₀ hcell f z hz hne
  apply mixedCoveredRowsSiteValue_mem_quarter rowSets U o b d z
    (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)))
    (fun j => mul_nonneg (hC j) (mul_nonneg (by positivity) (mul_nonneg (hT j) (hR j).le)))
    _ hbudget s
  intro j t
  obtain ⟨hr, hz⟩ := allocatedWindowMixed_coordinate_bounds B U b hR hσ S rowSets d x q y₀ hcell
    T hTi hTw hσ1 z hw hi (hf _ hl) j t
  exact mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j) (hC j)
    (mul_nonneg (hT j) (hR j).le) (hchart j) _ _ hr hz

end Erdos3.VectorPolynomial

end

end OAI
