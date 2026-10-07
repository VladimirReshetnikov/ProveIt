/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3

def formalBracketMatrixHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H) ^ n

def formalCurrentMatrixHeight (n H : ℕ) : ℕ := (n + 1) * (H * H) ^ n

def formalGeometryHeight (n r H : ℕ) : ℕ :=
  let M := max H (homogeneousIntersectionBasisHeight n r H)
  max M (max (formalCurrentMatrixHeight n M) (formalBracketMatrixHeight n M))

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

theorem exists_rational_formal_stage_geometry
    {L μ υ χ ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ]
    (b : Basis μ ℚ L) (w : μ → ℕ) (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (hU : BasisGradedSubmodule b w U.toSubmodule)
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (f : Basis ι ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H r : ℕ} (hH : 1 ≤ H)
    (hrU : 2 * Fintype.card υ + Fintype.card μ ≤ r)
    (hrK : Fintype.card υ + Fintype.card χ + Fintype.card μ ≤ r)
    (hrV : Fintype.card υ + Fintype.card ι + Fintype.card μ ≤ r)
    (hQU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (hQK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (hQV : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (hK : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (hstructure : ∀ i z k, RationalHeightLE (b.repr ⁅b i, b z⁆ k) H)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H),
      G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
  classical
  let J := homogeneousIntersectionBasisHeight (Fintype.card μ) r H
  let M := max H J
  let B := if j = 2 then K else V
  let Ebr := homogeneousIntersection b w (j - 1) U.toSubmodule B
  let Ecur := homogeneousIntersection b w j U.toSubmodule U.toSubmodule
  have hMout : M ≤ formalGeometryHeight (Fintype.card μ) r H := Nat.le_max_left _ _
  have hHout : H ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_left H J).trans hMout
  have hJout : J ≤ formalGeometryHeight (Fintype.card μ) r H := (Nat.le_max_right H J).trans hMout
  obtain ⟨eBr, heBr⟩ : ∃ e : Basis (Fin (Module.finrank ℚ Ebr)) ℚ Ebr,
      ∀ i z, RationalHeightLE (b.repr (e z : L) i) J := by
    by_cases hj2 : j = 2
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule K fU fK hH hrK hQU hQK
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule K :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = K from ite_eq_left hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
    · obtain ⟨e, he⟩ := exists_homogeneousIntersection_basis b w (j - 1) U.toSubmodule V fU f hH hrV hQU hQV
      have hE : Ebr = homogeneousIntersection b w (j - 1) U.toSubmodule V :=
        congrArg (homogeneousIntersection b w (j - 1) U.toSubmodule) (show B = V from ite_eq_right hj2)
      rw [hE]
      exact ⟨e, fun i z => he z i⟩
  obtain ⟨eCur, heCur⟩ := exists_homogeneousIntersection_basis b w j U.toSubmodule U.toSubmodule fU fU (r := r)
    hH (by omega) hQU hQU
  have hbrmem (x : ℝ ⊗[ℚ] L) : x ∈ Ebr.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ B.baseChange ℝ ∧
      basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  have hcurmem (x : ℝ ⊗[ℚ] L) : x ∈ Ecur.baseChange ℝ ↔
      x ∈ realificationLieSubalgebra U ∧ x ∈ realificationLieSubalgebra U ∧
      basisGradeProjection (b.baseChange ℝ) w j x = x := by
    rw [homogeneousIntersection_baseChange]
    exact mem_homogeneousIntersection _ _ _ _ _ _
  let G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j
      (formalGeometryHeight (Fintype.card μ) r H) := {
    bracketSpace := Ebr
    currentSpace := Ecur
    bracketRank := Module.finrank ℚ Ebr
    currentRank := Module.finrank ℚ Ecur
    bracketBasis := eBr
    currentBasis := eCur
    bracket_grade := fun x hx => (hbrmem x).mp hx |>.2.2
    bracket_U := fun x hx => (hbrmem x).mp hx |>.1
    bracket_K := by
      intro h x hx
      simpa only [B, ite_eq_left h] using ((hbrmem x).mp hx).2.1
    bracket_V := by
      intro h x hx
      simpa only [B, ite_eq_right (show j ≠ 2 by omega)] using ((hbrmem x).mp hx).2.1
    bracket_complete := by
      intro x hx hgrade hKx hVx
      apply (hbrmem x).mpr
      refine ⟨hx, ?_, hgrade⟩
      by_cases h : j = 2
      · simpa only [B, ite_eq_left h] using hKx h
      · simpa only [B, ite_eq_right h] using hVx (by omega)
    current_grade := fun x hx => (hcurmem x).mp hx |>.2.2
    current_U := fun x hx => (hcurmem x).mp hx |>.1
    current_projection := by
      intro x hx
      apply (hcurmem _).mpr
      have hp := hU.baseChange b w U.toSubmodule j x hx
      exact ⟨hp, hp, basisCoordinateProjection_idempotent (b.baseChange ℝ) {i | w i = j} x⟩
    bracket_matrix_height := by
      intro i z
      have h := bracketSystemMatrix_height b eBr f (fun k => (eK k : L))
        (fun i j k => (hstructure i j k).mono (Nat.le_max_left H J))
        (fun z i => (heBr i z).mono (Nat.le_max_right H J))
        (fun z i => (hK i z).mono (Nat.le_max_left H J))
        (fun i k => (hQV k i).mono (Nat.le_max_left H J)) i z
      exact h.mono ((Nat.le_max_right (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    current_matrix_height := by
      intro i z
      have h := subspaceQuotientMatrix_height b eCur f
        (fun i k => (hQV k i).mono (Nat.le_max_left H J))
        (fun z i => (heCur z i).mono (Nat.le_max_right H J)) i z
      exact h.mono ((Nat.le_max_left (formalCurrentMatrixHeight (Fintype.card μ) M)
        (formalBracketMatrixHeight (Fintype.card μ) M)).trans (Nat.le_max_right _ _))
    bracket_basis_height := fun i z => (heBr i z).mono hJout
    current_basis_height := fun i z => (heCur z i).mono hJout }
  exact ⟨G, homogeneousIntersection_finrank_le b w (j - 1) U.toSubmodule B,
    homogeneousIntersection_finrank_le b w j U.toSubmodule U.toSubmodule⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI
