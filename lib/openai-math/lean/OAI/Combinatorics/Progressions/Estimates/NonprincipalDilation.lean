import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) : Finset C := by
  classical
  exact Finset.univ.filter (fun j => e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal)

theorem mem_nonprincipalCoefficientSlots {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) :
    j ∈ nonprincipalCoefficientSlots e principal ↔
      e j ∈ fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  simp only [nonprincipalCoefficientSlots, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_monomialExponentSet {C K : Type*} [Fintype C]
    (e : C → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ monomialExponentSet e ↔ ∃ j, e j = m := by
  classical
  simp only [monomialExponentSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem mem_fixedNonprincipalExponents {B K : Type*} [Fintype B]
    (S : Finset (K →₀ ℕ)) (principal : B → K →₀ ℕ) (m : K →₀ ℕ) :
    m ∈ fixedNonprincipalExponents S principal ↔
      m ∈ S ∧ m ≠ 0 ∧ ∀ b, principal b ≠ m := by
  classical
  simp [fixedNonprincipalExponents]

theorem nonprincipalCoefficientSlots_image {C B K : Type*} [Fintype C] [Fintype B] [DecidableEq (K →₀ ℕ)]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) :
    (nonprincipalCoefficientSlots e principal).image e =
      fixedNonprincipalExponents (monomialExponentSet e) principal := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact (mem_nonprincipalCoefficientSlots e principal j).mp hj
  · intro hm
    have hs : m ∈ monomialExponentSet e :=
      ((mem_fixedNonprincipalExponents _ principal m).mp hm).1
    obtain ⟨j, rfl⟩ := (mem_monomialExponentSet e m).mp hs
    have hj := (mem_nonprincipalCoefficientSlots e principal j).mpr hm
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

theorem nonprincipalCoefficientSlots_sum {C B K R : Type*} [Fintype C] [Fintype B] [AddCommMonoid R]
    (e : C → K →₀ ℕ) (he : Function.Injective e) (principal : B → K →₀ ℕ) (f : (K →₀ ℕ) → R) :
    (∑ j ∈ nonprincipalCoefficientSlots e principal, f (e j)) =
      ∑ m ∈ fixedNonprincipalExponents (monomialExponentSet e) principal, f m := by
  classical
  rw [← nonprincipalCoefficientSlots_image e principal, Finset.sum_image (fun _ _ _ _ h => he h)]

theorem nonprincipalCoefficientSlots_not_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (b : B) (hj : e j = principal b) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.2
  exact hn b hj.symm

theorem nonprincipalCoefficientSlots_not_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (j : C) (hj : e j = 0) :
    j ∉ nonprincipalCoefficientSlots e principal := by
  classical
  intro hm
  have hn := ((mem_fixedNonprincipalExponents _ principal (e j)).mp
    ((mem_nonprincipalCoefficientSlots e principal j).mp hm)).2.1
  exact hn hj

theorem nonprincipalCoefficientSlots_degree {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {degree : ℕ}
    (he : ∀ j, (e j).sum (fun _ n => n) ≤ degree) :
    ∀ j ∈ nonprincipalCoefficientSlots e principal, (e j).sum (fun _ n => n) ≤ degree :=
  fun j _ => he j

end Erdos3

end

section

namespace Erdos3

noncomputable def nonprincipalDilation {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) : ℝ := by
  classical
  exact if j ∈ nonprincipalCoefficientSlots e principal then t else 1

theorem nonprincipalDilation_principal {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C) (b : B)
    (hj : e j = principal b) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_principal e principal j b hj, ite_false]

theorem nonprincipalDilation_zero {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : e j = 0) : nonprincipalDilation e principal t j = 1 := by
  classical
  simp only [nonprincipalDilation, nonprincipalCoefficientSlots_not_zero e principal j hj, ite_false]

theorem nonprincipalDilation_mem {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (t : ℝ) (j : C)
    (hj : j ∈ nonprincipalCoefficientSlots e principal) : nonprincipalDilation e principal t j = t := by
  classical
  simp only [nonprincipalDilation, hj, ite_true]

theorem nonprincipalDilation_pos {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t : ℝ} (ht : 0 < t) (j : C) :
    0 < nonprincipalDilation e principal t j := by
  classical
  unfold nonprincipalDilation
  split_ifs <;> positivity

theorem nonprincipalDilation_le_one {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t : ℝ} (ht : t ≤ 1) (j : C) :
    nonprincipalDilation e principal t j ≤ 1 := by
  classical
  unfold nonprincipalDilation
  split_ifs <;> linarith

theorem nonprincipalDilation_lower {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t : ℝ} (ht : t ≤ 1) (j : C) :
    t ≤ nonprincipalDilation e principal t j := by
  classical
  unfold nonprincipalDilation
  split_ifs <;> linarith

end Erdos3

end

end OAI
