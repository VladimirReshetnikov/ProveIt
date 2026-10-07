import OAI.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] F.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] F.squareLieSubalgebra)]

theorem realSquareObservable_lipschitz (e : Basis ι ℚ L) (b : Basis κ ℚ F.squareLieSubalgebra)
    (Γ : Subgroup F.Group) (l m H : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hSq : bchSubgroupCoordinates b (F.squareLattice Γ) ⊆ denominatorGrid m)
    (hfst : ∀ k i, RationalHeightLE (e.repr (F.squareFst (b i)) k) H)
    (hsnd : ∀ k i, RationalHeightLE (e.repr (F.squareSnd (b i)) k) H)
    (ε : F.realification.Group) (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (A K B : ℝ≥0)
    (hε : letI := realificationQuotientMetricSpace e Γ l hl hΓ
      LipschitzWith A (fun x : F.realification.Group ⧸ Γ.map realificationHom => ε • x))
    (hu : letI := realificationQuotientMetricSpace e Γ l hl hΓ; LipschitzWith K u)
    (hb : ∀ x, ‖u x‖ ≤ B) :
    let P := coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) H
    letI := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
    LipschitzWith (B * (K * P) + B * (K * (A * P))) (F.realSquareObservable Γ ε u) := by
  let := realificationQuotientMetricSpace e Γ l hl hΓ
  let := realificationQuotientMetricSpace b (F.squareLattice Γ) m hm hSq
  have hf := lipschitz_realificationMap_quotient b e F.squareFst (F.squareLattice Γ) Γ
    (F.squareLattice_le_fst Γ) m l hm hl hSq hΓ H hfst
  have hg := lipschitz_realificationMap_quotient b e F.squareSnd (F.squareLattice Γ) Γ
    (F.squareLattice_le_snd Γ) m l hm hl hSq hΓ H hsnd
  exact lipschitz_mul_star_of_bounds _ _ (hu.comp (hε.comp hf)) (hu.comp hg)
    (fun x => hb _) (fun x => hb _)

end Erdos3.NilpotentLieFiltration

end

end OAI
