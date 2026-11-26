/-
Direct interfaces for reusing lsernau/grh-lean.

STATUS: NOT LOCALLY COMPILED. No Lean executable was installed in the audit
environment. These are short source-level proof drafts, with no sorry or axiom.
Compile against repository commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Lean v4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

These lemmas do not formalize Dedekind-zeta factorization or a theorem for
general Hecke or automorphic L-functions. The generic product lemma can be
used once the relevant factorization and its factors are supplied separately.
-/
import Main

namespace GRHTransfer

open Complex DirichletCharacter
open scoped BigOperators

/-- A nonprincipal Dirichlet L-function has no real zero strictly above 1/2. -/
theorem real_nonprincipal_nonvanishing
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    LFunction χ (σ : ℂ) ≠ 0 := by
  apply LFunction_ne_zero_of_half_lt_re N χ (σ : ℂ)
  · simpa using hσ
  · exact Or.inl hχ

/-- A finite product of functions whose strip zeros lie on the critical line
has the same property. This is an algebraic interface, independent of GRH. -/
theorem finite_product_zero_on_line
    {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ)
    (hF : ∀ i ∈ S, ∀ s : ℂ,
      0 < s.re → s.re < 1 → F i s = 0 → s.re = 1 / 2)
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1)
    (hzero : (∏ i ∈ S, F i s) = 0) :
    s.re = 1 / 2 := by
  classical
  by_contra hline
  have hnonzero : (∏ i ∈ S, F i s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi hzero_i
    exact hline (hF i hi s hpos hlt hzero_i)
  exact hnonzero hzero

/-- Factors can have different moduli; each modulus is assumed nonzero. -/
theorem finite_dirichlet_product_zero_on_line
    {ι : Type*} (S : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1)
    (hzero : (∏ i ∈ S, LFunction (χ i) s) = 0) :
    s.re = 1 / 2 := by
  exact finite_product_zero_on_line S (fun i z ↦ LFunction (χ i) z)
    (fun i _ z hz0 hz1 hzi ↦ LFunction_eq_zero_re (q i) (χ i) z hz0 hz1 hzi)
    s hpos hlt hzero

/-- The same finite product is nonzero to the right of 1/2 when every factor's
possible principal pole is excluded. -/
theorem finite_dirichlet_product_nonvanishing
    {ι : Type*} (S : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hpole : ∀ i ∈ S, χ i ≠ 1 ∨ s ≠ 1) :
    (∏ i ∈ S, LFunction (χ i) s) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact LFunction_ne_zero_of_half_lt_re (q i) (χ i) s hs (hpole i hi)

end GRHTransfer

#print axioms GRHTransfer.real_nonprincipal_nonvanishing
#print axioms GRHTransfer.finite_product_zero_on_line
#print axioms GRHTransfer.finite_dirichlet_product_zero_on_line
#print axioms GRHTransfer.finite_dirichlet_product_nonvanishing
