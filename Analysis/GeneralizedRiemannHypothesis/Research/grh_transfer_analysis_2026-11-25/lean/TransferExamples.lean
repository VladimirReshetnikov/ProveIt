import Main

/-!
# Downstream interfaces for the grh-lean artifact

Status: source templates, NOT compiled or kernel-checked in this analysis.
Intended environment: the readable edition at commit
72fead102f663d5c7a407964a13dc0cf9d977207 with its pinned Lean and Mathlib.

Place this file in `grh/src/TransferExamples.lean`, build the project, and run:
  lake env lean src/TransferExamples.lean

These wrappers use the repository's exported theorems. They contain no admitted
proofs. They do not formalize a Dedekind-zeta factorization: such an identity is
an explicit input to the last theorem. No claim of new mathematical novelty is
made for these standard consequences.
-/

open scoped BigOperators

namespace GRHTransfer

/-- There are no real Dirichlet L-function zeros strictly between 1/2 and 1.
In particular, a real zero in the usual exceptional-zero region is excluded. -/
theorem noSiegelZeros
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  apply LFunction_ne_zero_of_half_lt_re N χ (σ : ℂ)
  · simpa using hhalf
  · right
    intro hs
    have hreal : σ = 1 := by simpa using congrArg Complex.re hs
    exact (ne_of_lt hone) hreal

/-- A finite product of Dirichlet L-functions has no zero right of 1/2,
provided each factor's pole exception is excluded. The moduli may vary. -/
theorem finiteProduct_nonzero
    {I : Type*} (S : Finset I) (N : I → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (s : ℂ) (hhalf : 1 / 2 < s.re)
    (hpole : ∀ i ∈ S, χ i ≠ 1 ∨ s ≠ 1) :
    (∏ i ∈ S, DirichletCharacter.LFunction (χ i) s) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact LFunction_ne_zero_of_half_lt_re (N i) (χ i) s hhalf (hpole i hi)

/-- Any zero in the critical strip of a finite Dirichlet L-product lies on
the critical line. -/
theorem finiteProduct_zero_on_line
    {I : Type*} (S : Finset I) (N : I → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i))
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1)
    (hzero : (∏ i ∈ S, DirichletCharacter.LFunction (χ i) s) = 0) :
    s.re = 1 / 2 := by
  classical
  obtain ⟨i, hi, hi_zero⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact LFunction_eq_zero_re (N i) (χ i) s hpos hlt hi_zero

/-- Transfer along an independently supplied identity with a Dirichlet
L-product. The factorization hypothesis is a genuine remaining obligation in
applications such as abelian Dedekind zeta functions. -/
theorem zero_on_line_of_dirichletFactorization
    {I : Type*} (S : Finset I) (N : I → ℕ) [∀ i, NeZero (N i)]
    (χ : ∀ i, DirichletCharacter ℂ (N i)) (F : ℂ → ℂ)
    (hfactor : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      F s = ∏ i ∈ S, DirichletCharacter.LFunction (χ i) s)
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) (hzero : F s = 0) :
    s.re = 1 / 2 := by
  apply finiteProduct_zero_on_line S N χ s hpos hlt
  rw [← hfactor s hpos hlt]
  exact hzero

#print axioms noSiegelZeros
#print axioms finiteProduct_nonzero
#print axioms finiteProduct_zero_on_line
#print axioms zero_on_line_of_dirichletFactorization

end GRHTransfer
