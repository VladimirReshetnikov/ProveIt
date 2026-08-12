import PolynomialFormulas.LazardQuinticAlternateProjection

/-!
# Recovering Lazard's four `Q₁` branches from the projection orbit

The four coherent sign changes of `(epsilon,T,U)` do not create new
projection data.  They permute the four source coordinates.  This module
records that permutation once and combines it with the standard inverse
projection formula.  The branch order is

`base, negateTU, rotate, rotateNegate  ↦  0, 2, 3, 1`.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false

section ProjectionBridge

variable {K : Type*} [Field K] [CharZero K]

/-- The source orbit reordered so that a sign branch recovers its zeroth
coordinate by the same standard inverse formula. -/
def sourceForBranch (source : Fin 4 → K) : SignBranch → Fin 4 → K
  | .base => ![source 0, source 1, source 2, source 3]
  | .negateTU => ![source 2, source 3, source 0, source 1]
  | .rotate => ![source 3, source 0, source 1, source 2]
  | .rotateNegate => ![source 1, source 2, source 3, source 0]

omit [CharZero K] in
/-- Changing the coherent signs and applying the corresponding source
permutation leaves all four standard projection values unchanged. -/
theorem standardProjections_branchTriple_sourceForBranch
    (v : QuadraticTriple K) (source : Fin 4 → K) (branch : SignBranch) :
    standardProjections
        (branchTriple v branch).epsilon
        (branchTriple v branch).t
        (branchTriple v branch).u
        (sourceForBranch source branch) =
      standardProjections v.epsilon v.t v.u source := by
  funext j
  cases branch <;> fin_cases j <;>
    simp [sourceForBranch, branchTriple, standardProjections,
      standardProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
/-- Changing the coherent signs and applying the corresponding source
permutation also leaves Lazard's alternate four projection values unchanged.

This is the invariant-theory input supplied by the alternate linear system:
once `(epsilon,T,U)` and the four-element source orbit transform coherently,
the degree-15 fourth projection is fixed without expanding its polynomial in
the five ordered roots. -/
theorem alternateProjections_branchTriple_sourceForBranch
    (v : QuadraticTriple K) (source : Fin 4 → K) (branch : SignBranch) :
    alternateProjections
        (branchTriple v branch).epsilon
        (branchTriple v branch).t
        (branchTriple v branch).u
        (sourceForBranch source branch) =
      alternateProjections v.epsilon v.t v.u source := by
  funext j
  cases branch <;> fin_cases j <;>
    simp [sourceForBranch, branchTriple, alternateProjections,
      alternateProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
/-- The convention-safe alternate row is likewise fixed under every
coherent sign/source branch. -/
theorem coherentAlternateProjections_branchTriple_sourceForBranch
    (v : QuadraticTriple K) (source : Fin 4 → K) (branch : SignBranch) :
    coherentAlternateProjections
        (branchTriple v branch).epsilon
        (branchTriple v branch).t
        (branchTriple v branch).u
        (sourceForBranch source branch) =
      coherentAlternateProjections v.epsilon v.t v.u source := by
  funext j
  cases branch <;> fin_cases j <;>
    simp [sourceForBranch, branchTriple, coherentAlternateProjections,
      coherentAlternateProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
/-- The transformation actually followed by the *printed Section-5* `U`
under multiplication by two is not the coherent `rotate` transformation:
`(epsilon,T,U)` goes to `(-epsilon,-U,T)`, whereas the source orbit goes to
`sourceForBranch source .rotate`.  The first two projections are fixed and
the last two acquire a minus sign. -/
theorem alternateProjections_sectionFiveU_multiplierTwo
    (epsilon t u : K) (source : Fin 4 → K) :
    alternateProjections (-epsilon) (-u) t
        (sourceForBranch source .rotate) =
      ![alternateProjections epsilon t u source 0,
        alternateProjections epsilon t u source 1,
        -alternateProjections epsilon t u source 2,
        -alternateProjections epsilon t u source 3] := by
  funext j
  fin_cases j <;>
    simp [sourceForBranch, alternateProjections,
      alternateProjectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

omit [CharZero K] in
/-- In particular, the Section-5-sign alternate fourth projection is an
anti-invariant for the multiplier-by-two generator. -/
theorem alternateProjection_fourth_sectionFiveU_multiplierTwo
    (epsilon t u : K) (source : Fin 4 → K) :
    alternateProjections (-epsilon) (-u) t
        (sourceForBranch source .rotate) 3 =
      -alternateProjections epsilon t u source 3 := by
  exact congrFun
    (alternateProjections_sectionFiveU_multiplierTwo
      epsilon t u source) 3

omit [CharZero K] in
/-- Multiplying the alternate fourth projection by `epsilon` cancels that
character, so the product is fixed by multiplication by two. -/
theorem epsilon_mul_alternateProjection_fourth_sectionFiveU_multiplierTwo
    (epsilon t u : K) (source : Fin 4 → K) :
    (-epsilon) *
        alternateProjections (-epsilon) (-u) t
          (sourceForBranch source .rotate) 3 =
      epsilon * alternateProjections epsilon t u source 3 := by
  rw [alternateProjection_fourth_sectionFiveU_multiplierTwo]
  ring

/-- A concrete characteristic-zero counterexample to the naive claim that
the Section-5-sign alternate fourth projection is itself fixed under the
multiplier-by-two transformation. -/
theorem alternateProjection_fourth_sectionFiveU_not_invariant :
      alternateProjections (-1 : ℚ) 0 1
        (sourceForBranch (![1, 0, 0, 0] : Fin 4 → ℚ) .rotate) 3 ≠
      alternateProjections 1 1 0 (![1, 0, 0, 0] : Fin 4 → ℚ) 3 := by
  have hbase : ∀ j : Fin 4,
      alternateProjections (1 : ℚ) 1 0 (![1, 0, 0, 0] : Fin 4 → ℚ) j = 1 := by
    intro j
    fin_cases j <;>
      norm_num [alternateProjections, alternateProjectionMatrix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have htransform :
      alternateProjections (-1 : ℚ) 0 1
          (sourceForBranch (![1, 0, 0, 0] : Fin 4 → ℚ) .rotate) 3 =
        -alternateProjections 1 1 0
          (![1, 0, 0, 0] : Fin 4 → ℚ) 3 := by
    simpa only [neg_zero] using
      (alternateProjection_fourth_sectionFiveU_multiplierTwo
        (1 : ℚ) 1 0 (![1, 0, 0, 0] : Fin 4 → ℚ))
  rw [htransform]
  rw [hbase 3]
  norm_num

/-- Section 7's scaled projection values make `Q₁` exactly the standard
recovery expression. -/
theorem q1_eq_standardRecover_of_projection_values
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (source : Fin 4 → K) (hrelations : QuadraticRelations c i v)
    (hepsilon : v.epsilon ≠ 0) (hE : invariantE c i ≠ 0)
    (hH : standardProjections v.epsilon v.t v.u source 0 =
      5 * invariantH c i)
    (hI : standardProjections v.epsilon v.t v.u source 1 =
      5 * invariantI c i)
    (hJ : standardProjections v.epsilon v.t v.u source 2 =
      (25 / 2) * invariantJ c i)
    (hK : standardProjections v.epsilon v.t v.u source 3 =
      (25 / 2) * invariantK c i) :
    q1 c i v =
      standardRecover v.epsilon v.t v.u
        (standardProjections v.epsilon v.t v.u source) := by
  rw [standardRecover, hH, hI, hJ, hK, hrelations.t_sq_add_u_sq]
  unfold q1
  field_simp [hepsilon, hE]
  ring

/-- Under the standard nonzero hypotheses, a coherent `Q₁` recovers the
zeroth coordinate of its projection source. -/
theorem q1_eq_source_zero_of_projection_values
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (source : Fin 4 → K) (hrelations : QuadraticRelations c i v)
    (hepsilon : v.epsilon ≠ 0) (hE : invariantE c i ≠ 0)
    (hH : standardProjections v.epsilon v.t v.u source 0 =
      5 * invariantH c i)
    (hI : standardProjections v.epsilon v.t v.u source 1 =
      5 * invariantI c i)
    (hJ : standardProjections v.epsilon v.t v.u source 2 =
      (25 / 2) * invariantJ c i)
    (hK : standardProjections v.epsilon v.t v.u source 3 =
      (25 / 2) * invariantK c i) :
    q1 c i v = source 0 := by
  have hdenominator : v.t ^ 2 + v.u ^ 2 ≠ 0 := by
    rw [hrelations.t_sq_add_u_sq]
    exact mul_ne_zero (by norm_num) hE
  calc
    q1 c i v =
        standardRecover v.epsilon v.t v.u
          (standardProjections v.epsilon v.t v.u source) :=
      q1_eq_standardRecover_of_projection_values source hrelations
        hepsilon hE hH hI hJ hK
    _ = source 0 :=
      standardRecover_standardProjections v.epsilon v.t v.u source
        hepsilon hdenominator

/-- Every coherent sign branch recovers the zeroth coordinate of its
correspondingly permuted source orbit. -/
theorem q1_branchTriple_eq_sourceForBranch_zero
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (source : Fin 4 → K) (hrelations : QuadraticRelations c i v)
    (hepsilon : v.epsilon ≠ 0) (hE : invariantE c i ≠ 0)
    (hH : standardProjections v.epsilon v.t v.u source 0 =
      5 * invariantH c i)
    (hI : standardProjections v.epsilon v.t v.u source 1 =
      5 * invariantI c i)
    (hJ : standardProjections v.epsilon v.t v.u source 2 =
      (25 / 2) * invariantJ c i)
    (hK : standardProjections v.epsilon v.t v.u source 3 =
      (25 / 2) * invariantK c i)
    (branch : SignBranch) :
    q1 c i (branchTriple v branch) =
      sourceForBranch source branch 0 := by
  have hproj :=
    standardProjections_branchTriple_sourceForBranch v source branch
  have hrelations' := hrelations.of_branchTriple branch
  have hepsilon' : (branchTriple v branch).epsilon ≠ 0 := by
    cases branch <;> simpa [branchTriple] using hepsilon
  apply q1_eq_source_zero_of_projection_values
    (sourceForBranch source branch) hrelations' hepsilon' hE
  · rw [hproj]
    exact hH
  · rw [hproj]
    exact hI
  · rw [hproj]
    exact hJ
  · rw [hproj]
    exact hK

/-- If one source coordinate is nonzero, one of Lazard's four coherent
`Q₁` branches is nonzero. -/
theorem exists_q1_branch_ne_zero_of_exists_source_ne_zero
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (source : Fin 4 → K) (hrelations : QuadraticRelations c i v)
    (hepsilon : v.epsilon ≠ 0) (hE : invariantE c i ≠ 0)
    (hH : standardProjections v.epsilon v.t v.u source 0 =
      5 * invariantH c i)
    (hI : standardProjections v.epsilon v.t v.u source 1 =
      5 * invariantI c i)
    (hJ : standardProjections v.epsilon v.t v.u source 2 =
      (25 / 2) * invariantJ c i)
    (hK : standardProjections v.epsilon v.t v.u source 3 =
      (25 / 2) * invariantK c i)
    (hsource : ∃ j : Fin 4, source j ≠ 0) :
    ∃ branch : SignBranch, q1 c i (branchTriple v branch) ≠ 0 := by
  obtain ⟨j, hj⟩ := hsource
  have hbranch := q1_branchTriple_eq_sourceForBranch_zero source hrelations
    hepsilon hE hH hI hJ hK
  fin_cases j
  · refine ⟨.base, ?_⟩
    rw [hbranch .base]
    simpa [sourceForBranch] using hj
  · refine ⟨.rotateNegate, ?_⟩
    rw [hbranch .rotateNegate]
    simpa [sourceForBranch] using hj
  · refine ⟨.negateTU, ?_⟩
    rw [hbranch .negateTU]
    simpa [sourceForBranch] using hj
  · refine ⟨.rotate, ?_⟩
    rw [hbranch .rotate]
    simpa [sourceForBranch] using hj

omit [CharZero K] in
/-- The finite selector is complete once mathematical existence of a nonzero
branch has been established. -/
theorem selectSignBranch_complete [DecidableEq K]
    (c : DepressedQuintic K) (i : Invariants K) (v : QuadraticTriple K)
    (hexists : ∃ branch : SignBranch,
      q1 c i (branchTriple v branch) ≠ 0) :
    ∃ branch : SignBranch, selectSignBranch c i v = some branch := by
  by_cases hbase : q1 c i (branchTriple v .base) ≠ 0
  · exact ⟨.base, by simp [selectSignBranch, hbase]⟩
  · by_cases hneg : q1 c i (branchTriple v .negateTU) ≠ 0
    · exact ⟨.negateTU, by simp [selectSignBranch, hbase, hneg]⟩
    · by_cases hrotate : q1 c i (branchTriple v .rotate) ≠ 0
      · exact ⟨.rotate, by
          simp [selectSignBranch, hbase, hneg, hrotate]⟩
      · by_cases hrotateNegate :
          q1 c i (branchTriple v .rotateNegate) ≠ 0
        · exact ⟨.rotateNegate, by
            simp [selectSignBranch, hbase, hneg, hrotate, hrotateNegate]⟩
        · obtain ⟨branch, hbranch⟩ := hexists
          cases branch with
          | base => exact (hbase hbranch).elim
          | negateTU => exact (hneg hbranch).elim
          | rotate => exact (hrotate hbranch).elim
          | rotateNegate => exact (hrotateNegate hbranch).elim

/-- A nonzero source coordinate therefore makes Lazard's concrete finite
branch selector return a branch. -/
theorem exists_selectSignBranch_eq_some_of_exists_source_ne_zero
    [DecidableEq K]
    {c : DepressedQuintic K} {i : Invariants K} {v : QuadraticTriple K}
    (source : Fin 4 → K) (hrelations : QuadraticRelations c i v)
    (hepsilon : v.epsilon ≠ 0) (hE : invariantE c i ≠ 0)
    (hH : standardProjections v.epsilon v.t v.u source 0 =
      5 * invariantH c i)
    (hI : standardProjections v.epsilon v.t v.u source 1 =
      5 * invariantI c i)
    (hJ : standardProjections v.epsilon v.t v.u source 2 =
      (25 / 2) * invariantJ c i)
    (hK : standardProjections v.epsilon v.t v.u source 3 =
      (25 / 2) * invariantK c i)
    (hsource : ∃ j : Fin 4, source j ≠ 0) :
    ∃ branch : SignBranch, selectSignBranch c i v = some branch :=
  selectSignBranch_complete c i v
    (exists_q1_branch_ne_zero_of_exists_source_ne_zero source hrelations
      hepsilon hE hH hI hJ hK hsource)

end ProjectionBridge

end LeanProofs.PolynomialFormulas.LazardQuintic
