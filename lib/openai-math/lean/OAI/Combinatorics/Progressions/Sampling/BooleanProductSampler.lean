/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {B F α : Type*} [Fintype B] [Fintype F] [Fintype α]
  [DecidableEq B] [DecidableEq F] [DecidableEq α]

noncomputable def booleanBlockPolynomial (b : B) (t : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  ∏ v : F, booleanAffinePolynomial b v t

noncomputable def booleanSamplerPolynomial (c : B → ℝ) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  booleanCoefficient (fun t => ∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial b t) s

noncomputable def booleanSelectedColumn (c : B → ℝ) (b : B) (v : F) (r : Option α) (s : Finset α) :
    MvPolynomial (BlockParameter B F α) ℝ :=
  MvPolynomial.C (c b) * booleanCoefficient
    (fun t => MvPolynomial.C (booleanFeature r t : ℝ) *
      ∏ k ∈ Finset.univ.erase v, booleanAffinePolynomial b k t) s

omit [Fintype B] in
theorem booleanBlockPolynomial_pderiv (b b₀ : B) (v₀ : F) (r : Option α) (t : Finset α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanBlockPolynomial (F := F) b t) =
      if b = b₀ then MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b k t else 0 := by
  by_cases hb : b = b₀
  · subst b
    rw [ite_eq_left rfl, booleanBlockPolynomial, pderiv_prod_one_active
      (b₀, v₀, r) Finset.univ (fun k => booleanAffinePolynomial b₀ k t) v₀ (Finset.mem_univ _)]
    · simp only [booleanAffinePolynomial_pderiv, and_self, ite_true]
    · intro k hk
      simp only [booleanAffinePolynomial_pderiv, true_and]
      exact ite_eq_right (Finset.ne_of_mem_erase hk)
  · rw [ite_eq_right hb, booleanBlockPolynomial]
    apply pderiv_prod_zero
    intro k _
    simp only [booleanAffinePolynomial_pderiv, hb, false_and, ite_false]

theorem booleanSamplerPolynomial_pderiv (c : B → ℝ) (s : Finset α) (b₀ : B) (v₀ : F) (r : Option α) :
    MvPolynomial.pderiv (b₀, v₀, r) (booleanSamplerPolynomial (F := F) c s) =
      booleanSelectedColumn c b₀ v₀ r s := by
  rw [booleanSamplerPolynomial, pderiv_booleanCoefficient]
  have hinner (t : Finset α) :
      MvPolynomial.pderiv (b₀, v₀, r)
        (∑ b : B, MvPolynomial.C (c b) * booleanBlockPolynomial (F := F) b t) =
      MvPolynomial.C (c b₀) * (MvPolynomial.C (booleanFeature r t : ℝ) *
        ∏ k ∈ Finset.univ.erase v₀, booleanAffinePolynomial b₀ k t) := by
    simp only [map_sum, MvPolynomial.pderiv_C_mul, booleanBlockPolynomial_pderiv, mul_ite, mul_zero]
    simp
  simp_rw [hinner]
  rw [booleanCoefficient_const_mul]
  rfl

omit [Fintype B] [DecidableEq B] in
theorem booleanSelectedColumn_specialization (c : B → ℝ) (label : B → F → Option α)
    (b : B) (v : F) (S s : Finset α)
    (hlabel : ∀ a, (∃ k, label b k = some a) ↔ a ∈ S) :
    MvPolynomial.eval (blockSpecialization label) (booleanSelectedColumn c b v (label b v) s) =
      c b * if s = S then 1 else 0 := by
  rw [booleanSelectedColumn, map_mul, MvPolynomial.eval_C, booleanCoefficient_map]
  have hinner (t : Finset α) :
      MvPolynomial.eval (blockSpecialization label)
        (MvPolynomial.C (booleanFeature (label b v) t : ℝ) *
          ∏ k ∈ Finset.univ.erase v, booleanAffinePolynomial b k t) =
      if S ⊆ t then (1 : ℝ) else 0 := by
    simp only [map_mul, MvPolynomial.eval_C, map_prod, booleanAffinePolynomial_specialization]
    rw [Finset.mul_prod_erase Finset.univ (fun k => (booleanFeature (label b k) t : ℝ)) (Finset.mem_univ v)]
    exact booleanFeature_product (label b) S hlabel t
  simp_rw [hinner]
  rw [booleanCoefficient_monomial]

end Erdos3

end

end OAI
