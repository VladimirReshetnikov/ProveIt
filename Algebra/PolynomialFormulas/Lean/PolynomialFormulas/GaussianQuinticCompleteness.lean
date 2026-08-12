import PolynomialFormulas.GaussianQuinticSolver

/-!
# Completeness and radical-solvability specification for the quintic solver

This module gives a precise meaning to the finite vector returned by
`GaussianQuinticSolver.solve`.  It proves two statements:

* whenever a finite vector is returned, it contains every complex root; and
* for every nonzero Gaussian-rational input, such a vector is returned if and
  only if every complex root is expressible by radicals.

The second statement is a classical specification of the existing
noncomputable dispatcher.  It does not turn the certificate search into an
executable algorithm.
-/

namespace LeanProofs.PolynomialFormulas

open Polynomial

noncomputable section

namespace GaussianQuinticSolver

/-! ## Semantic radical solvability for Gaussian-rational coefficients -/

/-- Root-set solvability for a polynomial over `ℂ`, measured in the radical
closure of `ℚ` in `ℂ`. -/
def ComplexCompletelySolvableByRadicals (p : ℂ[X]) : Prop :=
  ∀ x : p.rootSet ℂ, (x : ℂ) ∈ solvableByRad ℚ ℂ

/-- The complex-coefficient formulation agrees with the existing formulation
for a rational polynomial mapped into `ℂ`. -/
theorem completelySolvableByRadicals_map_iff (p : ℚ[X]) :
    LeanProofs.PolynomialFormulas.CompletelySolvableByRadicals p ↔
      ComplexCompletelySolvableByRadicals
        (p.map (algebraMap ℚ ℂ)) := by
  have hroots :
      (p.map (algebraMap ℚ ℂ)).rootSet ℂ = p.rootSet ℂ := by
    classical
    rw [rootSet_def, rootSet_def, aroots_map]
  simp only [LeanProofs.PolynomialFormulas.CompletelySolvableByRadicals,
    ComplexCompletelySolvableByRadicals]
  rw [hroots]

/-- The complex polynomial represented by a Gaussian-rational coefficient
tuple. -/
def Coefficients.complexPolynomial (c : Coefficients) : ℂ[X] :=
  monomial 5 (GaussianRat.toComplex c.a5) +
  monomial 4 (GaussianRat.toComplex c.a4) +
  monomial 3 (GaussianRat.toComplex c.a3) +
  monomial 2 (GaussianRat.toComplex c.a2) +
  monomial 1 (GaussianRat.toComplex c.a1) +
  monomial 0 (GaussianRat.toComplex c.a0)

@[simp]
theorem Coefficients.complexPolynomial_eval (c : Coefficients) (x : ℂ) :
    c.complexPolynomial.eval x = c.eval x := by
  simp [Coefficients.complexPolynomial, Coefficients.eval,
    Coefficients.toQuartic, GaussianPolynomialSolver.Coefficients.eval,
    quartic]
  ring

theorem Coefficients.complexPolynomial_natDegree (c : Coefficients)
    (h5 : c.a5 ≠ 0) : c.complexPolynomial.natDegree = 5 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    simp only [Coefficients.complexPolynomial, coeff_add, coeff_monomial]
    simp [show 5 ≠ n by omega, show 4 ≠ n by omega,
      show 3 ≠ n by omega, show 2 ≠ n by omega,
      show 1 ≠ n by omega, show 0 ≠ n by omega]
  · simpa [Coefficients.complexPolynomial, coeff_monomial] using
      GaussianRat.toComplex_ne_zero_of_ne_zero h5

/-- Semantic complete solvability for a Gaussian-rational coefficient tuple:
every complex zero belongs to the radical closure of `ℚ` in `ℂ`. -/
def Coefficients.CompletelySolvableByRadicals (c : Coefficients) : Prop :=
  ∀ x : ℂ, c.eval x = 0 → x ∈ solvableByRad ℚ ℂ

/-- Explicit per-root radical solvability for a Gaussian-rational tuple. -/
def Coefficients.HasCompleteRadicalSolution (c : Coefficients) : Prop :=
  ∀ x : ℂ, c.eval x = 0 → Nonempty (RadicalExpression x)

theorem Coefficients.hasCompleteRadicalSolution_iff (c : Coefficients) :
    c.HasCompleteRadicalSolution ↔ c.CompletelySolvableByRadicals := by
  simp only [Coefficients.HasCompleteRadicalSolution,
    Coefficients.CompletelySolvableByRadicals,
    RadicalExpression.nonempty_iff_mem_solvableByRad]

theorem Coefficients.completelySolvableByRadicals_iff_rootSet
    (c : Coefficients) (h5 : c.a5 ≠ 0) :
    c.CompletelySolvableByRadicals ↔
      ComplexCompletelySolvableByRadicals c.complexPolynomial := by
  have hpdeg := c.complexPolynomial_natDegree h5
  have hp0 : c.complexPolynomial ≠ 0 := by
    intro hp
    rw [hp, natDegree_zero] at hpdeg
    norm_num at hpdeg
  constructor
  · intro h x
    apply h x
    rw [← c.complexPolynomial_eval]
    simpa using (mem_rootSet_of_ne hp0).mp x.property
  · intro h x hx
    let y : c.complexPolynomial.rootSet ℂ :=
      ⟨x, (mem_rootSet_of_ne hp0).mpr (by simpa using hx)⟩
    exact h y

/-! ## Complete factorizations are equivalent to semantic solvability -/

/-- A complete five-expression factorization exists exactly for a genuine
quintic whose every complex root is solvable by radicals. -/
theorem completeRadicalSolution_iff (c : Coefficients) :
    Nonempty (CompleteRadicalSolution c) ↔
      c.a5 ≠ 0 ∧ c.CompletelySolvableByRadicals := by
  constructor
  · rintro ⟨solution⟩
    refine ⟨solution.leading_ne_zero, ?_⟩
    intro x hx
    rw [solution.factorization] at hx
    have hlead : GaussianRat.toComplex c.a5 ≠ 0 :=
      GaussianRat.toComplex_ne_zero_of_ne_zero solution.leading_ne_zero
    have hprod : ∏ k : Fin 5, (x - (solution.roots k).value) = 0 :=
      (mul_eq_zero.mp hx).resolve_left hlead
    rw [Finset.prod_eq_zero_iff] at hprod
    obtain ⟨k, _, hk⟩ := hprod
    have hxk : x = (solution.roots k).value := sub_eq_zero.mp hk
    rw [hxk]
    exact (solution.roots k).expression.eval_mem_solvableByRad
  · rintro ⟨h5, hsolvable⟩
    let p : ℂ[X] := c.complexPolynomial
    have hpdeg : p.natDegree = 5 := c.complexPolynomial_natDegree h5
    have hp0 : p ≠ 0 := by
      intro hp
      rw [hp, natDegree_zero] at hpdeg
      norm_num at hpdeg
    let rootsList : List ℂ := p.roots.toList
    have hlength : rootsList.length = 5 := by
      simp [rootsList, IsAlgClosed.card_roots_eq_natDegree, hpdeg]
    let rootValue : Fin 5 → ℂ := fun k =>
      rootsList.get (Fin.cast hlength.symm k)
    have hroot (k : Fin 5) : c.eval (rootValue k) = 0 := by
      rw [← c.complexPolynomial_eval]
      change p.eval (rootValue k) = 0
      apply (mem_roots hp0).mp
      exact Multiset.mem_toList.mp
        (rootsList.get_mem (Fin.cast hlength.symm k))
    let roots : Fin 5 → ExplicitRadical := fun k =>
      ⟨rootValue k, Classical.choice
        (RadicalExpression.nonempty_iff_mem_solvableByRad.mpr
          (hsolvable (rootValue k) (hroot k)))⟩
    refine ⟨⟨h5, roots, fun x => ?_⟩⟩
    rw [← c.complexPolynomial_eval]
    change p.eval x = _
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots]
    have hlead : p.leadingCoeff = GaussianRat.toComplex c.a5 := by
      rw [leadingCoeff, hpdeg]
      simp [p, Coefficients.complexPolynomial, coeff_monomial]
    rw [hlead]
    congr 1
    let f : ℂ → ℂ := fun z => x - z
    calc
      (p.roots.map (x - ·)).prod = (rootsList.map f).prod := by
        exact (Multiset.prod_map_toList p.roots f).symm
      _ = ∏ j : Fin rootsList.length, f (rootsList.get j) := by
        exact (Fin.prod_univ_fun_getElem rootsList f).symm
      _ = ∏ k : Fin 5,
          f (rootsList.get (Fin.cast hlength.symm k)) := by
        exact ((finCongr hlength.symm).prod_comp
          fun j => f (rootsList.get j)).symm
      _ = ∏ k : Fin 5, (x - (roots k).value) := by
        rfl

theorem completeRadicalSolution_iff_of_a5_ne_zero
    (c : Coefficients) (h5 : c.a5 ≠ 0) :
    Nonempty (CompleteRadicalSolution c) ↔
      c.CompletelySolvableByRadicals := by
  rw [completeRadicalSolution_iff]
  simp [h5]

theorem completeRadicalSolution_iff_hasCompleteRadicalSolution
    (c : Coefficients) (h5 : c.a5 ≠ 0) :
    Nonempty (CompleteRadicalSolution c) ↔
      c.HasCompleteRadicalSolution := by
  rw [completeRadicalSolution_iff_of_a5_ne_zero c h5,
    c.hasCompleteRadicalSolution_iff]

/-! ## The finite vector returned by the solver -/

/-- A length-indexed vector of explicit radical expressions. -/
structure RootVector where
  size : ℕ
  roots : Fin size → ExplicitRadical

namespace RootVector

/-- Regard a finite list as a length-indexed vector. -/
def ofList (roots : List ExplicitRadical) : RootVector :=
  ⟨roots.length, roots.get⟩

/-- Membership by represented complex value. -/
def Contains (v : RootVector) (x : ℂ) : Prop :=
  ∃ k, (v.roots k).value = x

theorem ofList_contains_iff (roots : List ExplicitRadical) (x : ℂ) :
    (ofList roots).Contains x ↔ ∃ r ∈ roots, r.value = x := by
  simp only [Contains, ofList]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨roots.get k, List.get_mem roots k, hk⟩
  · rintro ⟨r, hr, hx⟩
    obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hr
    exact ⟨k, hx⟩

/-- The product represented by a leading value and a root vector. -/
def productValue (leading : ℂ) (v : RootVector) (x : ℂ) : ℂ :=
  leading * ∏ k, (x - (v.roots k).value)

/-- An exact factorization with nonzero leading value makes vector membership
equivalent to being a polynomial root. -/
theorem eval_eq_zero_iff_contains {c : Coefficients} {v : RootVector}
    {leading : ℂ} (hleading : leading ≠ 0)
    (hfactor : ∀ x, c.eval x = v.productValue leading x) (x : ℂ) :
    c.eval x = 0 ↔ v.Contains x := by
  rw [hfactor]
  simp only [productValue, mul_eq_zero, hleading, false_or,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, Contains]
  constructor
  · rintro ⟨k, hx⟩
    exact ⟨k, (sub_eq_zero.mp hx).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, sub_self _⟩

end RootVector

namespace Coefficients

/-- The input is not the identically-zero coefficient tuple. -/
def Nonzero (c : Coefficients) : Prop :=
  c.a5 ≠ 0 ∨ c.a4 ≠ 0 ∨ c.a3 ≠ 0 ∨
    c.a2 ≠ 0 ∨ c.a1 ≠ 0 ∨ c.a0 ≠ 0

end Coefficients

namespace Result

/-- Extract the finite vector represented by a result.  The identically-zero
lower-degree result and `unsupported` do not represent finite vectors. -/
def rootVector? {c : Coefficients} : Result c → Option RootVector
  | .lowerDegree _ =>
      match GaussianPolynomialSolver.solve c.toQuartic with
      | .identicallyZero => none
      | .finite data => some (RootVector.ofList data.roots)
  | .lazardCandidates solution => some ⟨5, solution.roots⟩
  | .completeRadical solution => some ⟨5, solution.roots⟩
  | .unsupported => none

/-- A result actually returned a finite vector of radical expressions. -/
def HasRootVector {c : Coefficients} (result : Result c) : Prop :=
  ∃ roots, result.rootVector? = some roots

/-- Whenever a vector can be extracted, it comes with a nonzero-leading exact
factorization. -/
def HasExactFactorization {c : Coefficients} (result : Result c) : Prop :=
  ∀ roots, result.rootVector? = some roots →
    ∃ leading : ℂ, leading ≠ 0 ∧
      ∀ x, c.eval x = roots.productValue leading x

/-- Every proof-carrying result has an exact factorization for each vector it
actually returns. -/
theorem hasExactFactorization {c : Coefficients} (result : Result c) :
    result.HasExactFactorization := by
  cases result with
  | lowerDegree h5 =>
      intro roots hroots
      cases hs : GaussianPolynomialSolver.solve c.toQuartic with
      | identicallyZero =>
          simp [rootVector?, hs] at hroots
      | finite data =>
          simp only [rootVector?, hs, Option.some.injEq] at hroots
          subst roots
          refine ⟨data.leading.value, data.leading_ne_zero, ?_⟩
          intro x
          rw [c.eval_eq_toQuartic_eval_of_a5_eq_zero h5]
          rw [GaussianPolynomialSolver.solve_factorization, hs]
          simp only [GaussianPolynomialSolver.RootDescription.productValue,
            RootVector.productValue, RootVector.ofList]
          congr 1
          exact (Fin.prod_univ_fun_getElem data.roots
            (fun r => x - r.value)).symm
  | lazardCandidates solution =>
      intro roots hroots
      simp only [rootVector?, Option.some.injEq] at hroots
      subst roots
      exact ⟨GaussianRat.toComplex c.a5,
        GaussianRat.toComplex_ne_zero_of_ne_zero solution.leading_ne_zero,
        solution.factorization⟩
  | completeRadical solution =>
      intro roots hroots
      simp only [rootVector?, Option.some.injEq] at hroots
      subst roots
      exact ⟨GaussianRat.toComplex c.a5,
        GaussianRat.toComplex_ne_zero_of_ne_zero solution.leading_ne_zero,
        solution.factorization⟩
  | unsupported =>
      intro _ hroots
      simp [rootVector?] at hroots

/-- Every complex root occurs in any vector extracted from a result. -/
theorem returnedVector_is_complete {c : Coefficients} (result : Result c)
    {roots : RootVector} (hroots : result.rootVector? = some roots) :
    ∀ x : ℂ, c.eval x = 0 → roots.Contains x := by
  intro x hx
  obtain ⟨leading, hleading, hfactor⟩ :=
    result.hasExactFactorization roots hroots
  exact (RootVector.eval_eq_zero_iff_contains hleading hfactor x).mp hx

/-- Exact root-set characterization for any vector extracted from a result. -/
theorem eval_eq_zero_iff_rootVector_contains {c : Coefficients}
    (result : Result c) {roots : RootVector}
    (hroots : result.rootVector? = some roots) (x : ℂ) :
    c.eval x = 0 ↔ roots.Contains x := by
  obtain ⟨leading, hleading, hfactor⟩ :=
    result.hasExactFactorization roots hroots
  exact RootVector.eval_eq_zero_iff_contains hleading hfactor x

/-- Returning a finite radical vector implies semantic complete solvability. -/
theorem completelySolvableByRadicals_of_hasRootVector
    {c : Coefficients} (result : Result c) (hroots : result.HasRootVector) :
    c.CompletelySolvableByRadicals := by
  obtain ⟨roots, hroots⟩ := hroots
  intro x hx
  obtain ⟨k, hk⟩ := result.returnedVector_is_complete hroots x hx
  subst x
  exact (roots.roots k).expression.eval_mem_solvableByRad

end Result

/-! ## Public solver specifications -/

/-- A zero leading coefficient and a nonzero input force the delegated
degree-at-most-four solver to return a finite result. -/
private theorem lowerDegree_hasRootVector (c : Coefficients)
    (hc : c.Nonzero) (h5 : c.a5 = 0) :
    (Result.lowerDegree h5).HasRootVector := by
  have hsne : GaussianPolynomialSolver.solve c.toQuartic ≠
      .identicallyZero := by
    intro hs
    have h4 : c.a4 = 0 := by
      by_contra h4
      simp [GaussianPolynomialSolver.solve, Coefficients.toQuartic, h4] at hs
    have h3 : c.a3 = 0 := by
      by_contra h3
      simp [GaussianPolynomialSolver.solve, Coefficients.toQuartic, h4, h3] at hs
    have h2 : c.a2 = 0 := by
      by_contra h2
      simp [GaussianPolynomialSolver.solve, Coefficients.toQuartic,
        h4, h3, h2] at hs
    have h1 : c.a1 = 0 := by
      by_contra h1
      simp [GaussianPolynomialSolver.solve, Coefficients.toQuartic,
        h4, h3, h2, h1] at hs
    have h0 : c.a0 = 0 := by
      by_contra h0
      simp [GaussianPolynomialSolver.solve, Coefficients.toQuartic,
        h4, h3, h2, h1, h0] at hs
    simp [Coefficients.Nonzero, h5, h4, h3, h2, h1, h0] at hc
  cases hs : GaussianPolynomialSolver.solve c.toQuartic with
  | identicallyZero => exact (hsne hs).elim
  | finite data =>
      exact ⟨RootVector.ofList data.roots, by
        simp [Result.rootVector?, hs]⟩

/-- For every nonzero input, the solver returns a finite vector of radical
expressions if and only if every complex root is solvable by radicals. -/
theorem solve_hasRootVector_iff_completelySolvableByRadicals
    (c : Coefficients) (hc : c.Nonzero) :
    (solve c).HasRootVector ↔ c.CompletelySolvableByRadicals := by
  constructor
  · exact Result.completelySolvableByRadicals_of_hasRootVector (solve c)
  · intro hsolvable
    by_cases h5 : c.a5 = 0
    · rw [solve_of_a5_eq_zero c h5]
      exact lowerDegree_hasRootVector c hc h5
    · have hSolution : Nonempty (CompleteRadicalSolution c) :=
        (completeRadicalSolution_iff_of_a5_ne_zero c h5).mpr hsolvable
      classical
      by_cases hLazard : Nonempty (LazardWitness c)
      · simp [solve, solveWith, h5, lazardBackend, hLazard,
          Result.HasRootVector, Result.rootVector?]
      · simp [solve, solveWith, h5, lazardBackend, hLazard, hSolution,
          Result.HasRootVector, Result.rootVector?]

/-- If `solve` returns a vector, every complex root of the input polynomial
appears in that vector. -/
theorem solve_returnedVector_is_complete (c : Coefficients)
    {roots : RootVector} (hroots : (solve c).rootVector? = some roots) :
    ∀ x : ℂ, c.eval x = 0 → roots.Contains x :=
  (solve c).returnedVector_is_complete hroots

/-- A returned vector contains exactly all complex roots of the input. -/
theorem solve_eval_eq_zero_iff_returnedVector_contains (c : Coefficients)
    {roots : RootVector} (hroots : (solve c).rootVector? = some roots)
    (x : ℂ) :
    c.eval x = 0 ↔ roots.Contains x :=
  (solve c).eval_eq_zero_iff_rootVector_contains hroots x

end GaussianQuinticSolver

end

end LeanProofs.PolynomialFormulas
