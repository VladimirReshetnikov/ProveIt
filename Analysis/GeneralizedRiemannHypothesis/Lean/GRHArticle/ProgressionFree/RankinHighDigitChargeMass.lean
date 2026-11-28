import GRHArticle.ProgressionFree.RankinHighDigitChargeMap
import GRHArticle.ProgressionFree.LightPrimeBlocks
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Reciprocal mass of high-digit charges

The injective assignment of a missing greedy vector and a mask gives each
admitted bad-high vector the product of the corresponding reciprocal weights.
Summing over all possible assigned data provides the desired upper bound.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The total mass of admitted bad-high vectors is at most the total missing
greedy mass times the sum of the two mask masses. -/
theorem reciprocalExponentMass_rankinBadHigh_le {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1)
    (k : ι → ℕ) {F : Set (ι → ℕ)} (hF : ThreeAPFree F) :
    reciprocalExponentMass u (rankinBadHighVectors k F) ≤
      reciprocalExponentMass u (rankinExponentVectors ι \ F) *
        ∑ e : Fin 2, reciprocalExponentMass (fun i ↦ u i^(e.val+1)) (rankinHighDigitMasks k) := by
  let A := ↥(rankinExponentVectors ι \ F)
  let D := ↥(rankinHighDigitMasks k)
  let w (a : A) := reciprocalExponentWeight u a.val
  let g (e : Fin 2) (d : D) := reciprocalExponentWeight (fun i ↦ u i^(e.val+1)) d.val
  let v (p : Fin 2 × D) := g p.1 p.2
  have hw₀ (a : A) : 0 ≤ w a := reciprocalExponentWeight_nonneg hu _
  have hg₀ (e : Fin 2) (d : D) : 0 ≤ g e d :=
    reciprocalExponentWeight_nonneg (fun i ↦ pow_nonneg (hu i) _) _
  have hu' := summable_reciprocalExponentWeight hu h₁
  have hw : Summable w := hu'.subtype _
  have hg (e : Fin 2) : Summable (g e) :=
    (summable_reciprocalExponentWeight (u := fun i ↦ u i^(e.val+1)) (fun i ↦ pow_nonneg (hu i) _)
      (fun i ↦ pow_lt_one₀ (hu i) (h₁ i) (by omega))).subtype _
  have hv : Summable v :=
    (summable_prod_of_nonneg (fun p ↦ hg₀ p.1 p.2)).mpr ⟨hg,(hasSum_fintype _).summable⟩
  have hProd : Summable (fun p : A × (Fin 2 × D) ↦ w p.1 * v p.2) :=
    hw.mul_of_nonneg hv hw₀ (fun p ↦ hg₀ p.1 p.2)
  let e := rankinHighDigitChargeEmbedding k hF
  have hWeight (s : ↥(rankinBadHighVectors k F)) :
      reciprocalExponentWeight u s.val = w (e s).1 * v (e s).2 := by
    dsimp only [w,v,g,reciprocalExponentWeight]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [rankinHighDigitChargeEmbedding_apply k hF s i,pow_add,pow_mul]
  rw [reciprocalExponentMass_eq_tsum_subtype,reciprocalExponentMass_eq_tsum_subtype]
  calc
    _ ≤ ∑' p : A × (Fin 2 × D), w p.1 * v p.2 :=
      Summable.tsum_le_tsum_of_inj e e.injective (fun p _ ↦ mul_nonneg (hw₀ p.1) (hg₀ p.2.1 p.2.2))
        (fun s ↦ (hWeight s).le) (hu'.subtype _) hProd
    _ = (∑' a : A, w a) * ∑' p : Fin 2 × D, v p := (hw.tsum_mul_tsum hv hProd).symm
    _ = _ := by
      have he : (∑' p : Fin 2 × D, v p) = ∑ j : Fin 2, ∑' d : D, g j d :=
        (hv.tsum_prod' hg).trans (tsum_fintype _)
      rw [he]
      simp only [reciprocalExponentMass_eq_tsum_subtype]
      rfl

end GRHArticle.ProgressionFree
