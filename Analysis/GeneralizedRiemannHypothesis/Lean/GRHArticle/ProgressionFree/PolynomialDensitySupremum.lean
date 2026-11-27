import GRHArticle.ProgressionFree.PolynomialBlocks

/-!
# The supremum of progression-free upper densities over a finite field
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

/-- There is no triple of nonzero polynomials with a positive-degree polynomial ratio. -/
def PolynomialRatioThreeGPFree {F : Type*} [Field F] (E : Set (Polynomial F)) : Prop :=
  ∀ f r, f ≠ 0 → 0 < r.natDegree → ¬ (f ∈ E ∧ f*r ∈ E ∧ f*r*r ∈ E)

/-- The article's `β_q`, the supremum over all sets free of polynomial-ratio triples. -/
noncomputable def polynomialRatioDensitySupremum (F : Type*) [Field F] [Fintype F] : ℝ :=
  sSup {d : ℝ | ∃ E : Set (Polynomial F), PolynomialRatioThreeGPFree E ∧
    d = limsup (polynomialBallProportion E) atTop}

variable {F : Type*} [Field F] [Fintype F]

theorem polynomialBallProportion_nonneg (E : Set (Polynomial F)) (n : ℕ) :
    0 ≤ polynomialBallProportion E n := by
  unfold polynomialBallProportion
  positivity

theorem limsup_polynomialBallProportion_le_one (E : Set (Polynomial F)) :
    limsup (polynomialBallProportion E) atTop ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop (polynomialBallProportion_nonneg E))
    (Eventually.of_forall (polynomialBallProportion_le_one E))

theorem le_polynomialRatioDensitySupremum {E : Set (Polynomial F)} (h : PolynomialRatioThreeGPFree E) :
    limsup (polynomialBallProportion E) atTop ≤ polynomialRatioDensitySupremum F := by
  refine le_csSup ⟨1, ?_⟩ ⟨E, h, rfl⟩
  rintro d ⟨S, _, rfl⟩
  exact limsup_polynomialBallProportion_le_one S

end GRHArticle.ProgressionFree
