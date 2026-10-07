/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.RealifiedTripleLayers

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    F.additiveTripleSubalgebra i hi c hc →ₗ⁅ℚ⁆ L :=
  (liePiEval j).comp (F.additiveTripleToPi i hi c hc)

@[simp] theorem additiveTripleProjection_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 0 = F.additiveTripleFirst i hi c hc := rfl

@[simp] theorem additiveTripleProjection_one (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 1 = F.additiveTripleSecond i hi c hc := rfl

@[simp] theorem additiveTripleProjection_two (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    F.additiveTripleProjection i hi c hc 2 = F.additiveTripleThird i hi c hc := rfl

noncomputable def realAdditiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    (F.additiveTripleFiltration i hi c hc).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.additiveTripleFiltration i hi c hc).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.additiveTripleProjection i hi c hc j)

theorem realifiedAdditiveTripleEquiv_projection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc x).val j =
      realificationLieHom (F.additiveTripleProjection i hi c hc j) x := by
  rw [F.realifiedAdditiveTripleEquiv_coe]
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [realificationLieHom_tmul, realTripleEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realAdditiveTripleProjection_coord (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group) :
    (F.realAdditiveTripleProjection i hi c hc j g).coord =
      tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc g.coord).val j :=
  (F.realifiedAdditiveTripleEquiv_projection i hi c hc j g.coord).symm

theorem realAdditiveTripleProjection_jointly_injective (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {g h : (F.additiveTripleFiltration i hi c hc).realification.Group}
    (heq : ∀ j, F.realAdditiveTripleProjection i hi c hc j g =
      F.realAdditiveTripleProjection i hi c hc j h) : g = h := by
  apply NilpotentLieBCHGroup.ext
  apply (F.realifiedAdditiveTripleEquiv i hi c hc).injective
  apply Subtype.ext
  apply tripleToPi_injective
  funext j
  simpa only [F.realAdditiveTripleProjection_coord] using
    congrArg NilpotentLieBCHGroup.coord (heq j)

end Erdos3.MultidegreeLieFiltration

end

end OAI
