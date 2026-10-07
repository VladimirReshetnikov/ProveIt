import OAI.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree
import OAI.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
import OAI.Combinatorics.Progressions.Estimates.MultidegreeIntegralModel

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShiftQuotient_integral_model (t l : ℕ) (hl : 0 < l) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
        B ≤ bchIntegralDenominatorBound (s + 1) *
          markedQuotientHeight s (Fintype.card ι) a d m q H ^ (q ^ 3) * l ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧ D.grid = B ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
            ∀ p : ℝ, (q : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p →
              (markedQuotientHeight s (Fintype.card ι) a d m q H : ℝ) ≤ Real.exp p →
              M.ComplexityLE p := by
  classical
  obtain ⟨m, hm, q, hq, f, hstructure, hlayers⟩ :=
    exists_markedShiftQuotient_bounded_data F b ω hF hω v w marked hw hv hH hc hgen t
  choose c hcoords using hlayers
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, _, hgrid, hcoord, hcomplex⟩ :=
    M₀.exists_bounded_integral_model f c hcoords hstructure l hl
  exact ⟨m, hm, q, hq, B, hB, hdiv, hbound, D, M, hMF, hgrid, hcoord, hcomplex⟩

end Erdos3

end

end OAI
