import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic

/-!
# Even multiplicity of roots of nonnegative polynomials

The real-root step in `trigonometry:lem:twosquares` and the positivity
argument of `trigonometry:thm:fejer`. These results hold over every ordered
field, including non-Archimedean fields. The order topology is used only
to preserve the sign of the nonvanishing residual factor near a root.
-/

namespace Surreal.FinitePolynomial

open Polynomial Filter Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- An odd-multiplicity real root forces a negative value somewhere in the field. -/
theorem exists_eval_neg_of_odd_rootMultiplicity (p : F[X]) (a : F)
    (hodd : Odd (p.rootMultiplicity a)) : ∃ x : F, p.eval x < 0 := by
  letI : TopologicalSpace F := Preorder.topology F
  letI : OrderTopology F := ⟨rfl⟩
  have hp : p ≠ 0 := by
    intro he
    simp only [he, rootMultiplicity_zero] at hodd
    exact (Nat.not_odd_zero hodd)
  obtain ⟨q, he, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hqa : q.eval a ≠ 0 := by
    simpa only [dvd_iff_isRoot, IsRoot] using hq
  have hv (x : F) : p.eval x = (x - a) ^ p.rootMultiplicity a * q.eval x := by
    conv_lhs => rw [he]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  rcases lt_or_gt_of_ne hqa with hneg | hpos
  · have hn : ∀ᶠ x in 𝓝 a, q.eval x < 0 := q.continuousAt.eventually (gt_mem_nhds hneg)
    obtain ⟨x, hx, hqx⟩ := ((frequently_gt_nhds a).and_eventually hn).exists
    refine ⟨x, ?_⟩
    rw [hv]
    exact mul_neg_of_pos_of_neg (pow_pos (sub_pos.mpr hx) _) hqx
  · have hn : ∀ᶠ x in 𝓝 a, 0 < q.eval x := q.continuousAt.eventually (lt_mem_nhds hpos)
    obtain ⟨x, hx, hqx⟩ := ((frequently_lt_nhds a).and_eventually hn).exists
    refine ⟨x, ?_⟩
    rw [hv]
    exact mul_neg_of_neg_of_pos (hodd.pow_neg (sub_neg.mpr hx)) hqx

/-- Nonnegativity at all field elements forces every real root multiplicity to be even. -/
theorem even_rootMultiplicity_of_nonnegative (p : F[X])
    (hp : ∀ x : F, 0 ≤ p.eval x) (a : F) : Even (p.rootMultiplicity a) := by
  by_contra h
  obtain ⟨x, hx⟩ := exists_eval_neg_of_odd_rootMultiplicity p a (Nat.not_even_iff_odd.mp h)
  exact (not_lt_of_ge (hp x)) hx

/-- Removing an even linear power preserves nonnegativity, including at the removed root. -/
theorem nonnegative_of_even_linear_factor (q : F[X]) (a : F) (m : ℕ) (hm : Even m)
    (hp : ∀ x : F, 0 ≤ ((X - C a) ^ m * q).eval x) :
    ∀ x : F, 0 ≤ q.eval x := by
  letI : TopologicalSpace F := Preorder.topology F
  letI : OrderTopology F := ⟨rfl⟩
  have haway (x : F) (hx : x ≠ a) : 0 ≤ q.eval x := by
    have he := hp x
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at he
    exact (mul_nonneg_iff_of_pos_left (hm.pow_pos (sub_ne_zero.mpr hx))).mp he
  intro x
  by_cases hx : x = a
  · subst x
    by_contra hn
    have hn' : ∀ᶠ y in 𝓝 a, q.eval y < 0 :=
      q.continuousAt.eventually (gt_mem_nhds (lt_of_not_ge hn))
    obtain ⟨y, hy, hqy⟩ := ((frequently_gt_nhds a).and_eventually hn').exists
    exact (not_lt_of_ge (haway y (ne_of_gt hy))) hqy
  · exact haway x hx

/-- Extract the full real-root multiplicity while retaining a nonnegative residual factor. -/
theorem nonnegative_root_factorization (p : F[X]) (hp : p ≠ 0)
    (hn : ∀ x : F, 0 ≤ p.eval x) (a : F) :
    ∃ m : ℕ, ∃ q : F[X], p.rootMultiplicity a = 2 * m ∧
      p = (X - C a) ^ (2 * m) * q ∧ (∀ x : F, 0 ≤ q.eval x) ∧ 0 < q.eval a := by
  obtain ⟨m, hm⟩ := even_rootMultiplicity_of_nonnegative p hn a
  have hm' : p.rootMultiplicity a = 2 * m := by omega
  obtain ⟨q, he, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have he' : p = (X - C a) ^ (2 * m) * q := by simpa only [hm'] using he
  have hqn : ∀ x : F, 0 ≤ q.eval x :=
    nonnegative_of_even_linear_factor q a (2 * m) (even_two_mul m)
      (fun x => by rw [← he']; exact hn x)
  have hqa : q.eval a ≠ 0 := by simpa only [dvd_iff_isRoot, IsRoot] using hq
  exact ⟨m, q, hm', he', hqn, lt_of_le_of_ne (hqn a) hqa.symm⟩

end Surreal.FinitePolynomial
