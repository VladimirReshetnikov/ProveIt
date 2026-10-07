import OAI.Combinatorics.Progressions.Estimates.MultidegreePredecessor

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairDegreeLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.dilationPairLayer q a

theorem dilationPairLayer_le_degree (q : ℚ) (n : ℕ) (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
    F.dilationPairLayer q a ≤ F.dilationPairDegreeLayer q n :=
  le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem dilationPairDegreeLayer_le_ordinary (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n ≤ F.ordinary.dilationPairLayer q n := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha
  exact (F.dilationPairLayer_le_ordinary q a).trans (F.ordinary.dilationPairLayer_antitone q ha)

theorem dilationPairDegree_higher (q : ℚ) (n : ℕ) (c d : ℚ) {x : L}
    (hx : x ∈ F.ordinary.layer (n + 1)) : (c • x, d • x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := (c • LinearMap.id).prod (d • LinearMap.id)
  have hφ : F.ordinary.layer (n + 1) ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro b
    apply iSup_le
    intro hb x hx
    obtain ⟨a, hab, ha⟩ := multidegree_exists_predecessor_above b n hb
    apply F.dilationPairLayer_le_degree q n a ha
    exact F.dilationPairLayer_of_strictUpper q a
      ((F.strictUpperLayer a).smul_mem c (F.layer_le_strictUpperLayer hab hx))
      ((F.strictUpperLayer a).smul_mem d (F.layer_le_strictUpperLayer hab hx))
  exact hφ hx

theorem dilationPairDegree_diagonal (q : ℚ) (n : ℕ) {x : L}
    (hx : x ∈ F.ordinary.layer n) : (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n := by
  let φ : L →ₗ[ℚ] L × L := ((q ^ n) • LinearMap.id).prod LinearMap.id
  have hφ : F.ordinary.layer n ≤ (F.dilationPairDegreeLayer q n).comap φ := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha x hx
    change (q ^ n • x, x) ∈ F.dilationPairDegreeLayer q n
    by_cases hna : n = ∑ i, a i
    · apply F.dilationPairLayer_le_degree q n a ha
      simpa only [hna] using F.dilationPairLayer_diagonal q a hx
    · have hhigh : x ∈ F.ordinary.layer (n + 1) :=
        F.ordinary.antitone (by omega : n + 1 ≤ ∑ i, a i) (F.layer_le_ordinary a hx)
      simpa only [one_smul] using F.dilationPairDegree_higher q n (q ^ n) 1 hhigh
  exact hφ hx

theorem dilationPairDegreeLayer_eq (q : ℚ) (n : ℕ) :
    F.dilationPairDegreeLayer q n = F.ordinary.dilationPairLayer q n := by
  apply le_antisymm (F.dilationPairDegreeLayer_le_ordinary q n)
  intro x hx
  have hleft : (x.1 - q ^ n • x.2, (0 : L)) ∈ F.dilationPairDegreeLayer q n := by
    simpa only [one_smul, zero_smul, scaledPairDifference_apply] using
      F.dilationPairDegree_higher q n 1 0 hx.2.2
  have hright := F.dilationPairDegree_diagonal q n hx.2.1
  have heq : x = (x.1 - q ^ n • x.2, (0 : L)) + (q ^ n • x.2, x.2) := by
    apply Prod.ext <;> simp
  rw [heq]
  exact (F.dilationPairDegreeLayer q n).add_mem hleft hright

end Erdos3.MultidegreeLieFiltration

end

end OAI
