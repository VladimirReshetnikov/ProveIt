/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_uniform_family_member_net {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ 2 * ε := by
  classical
  let occupied (i : I) : Prop := ∃ x, ∀ y, ‖F x y - centers i y‖ ≤ ε
  let rep (i : I) : X := if h : occupied i then h.choose else Classical.choice inferInstance
  have hrep (i : I) (hi : occupied i) : ∀ y, ‖F (rep i) y - centers i y‖ ≤ ε := by
    simp only [rep, dite_eq_left hi]
    exact hi.choose_spec
  refine ⟨rep, ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hnet x
  refine ⟨i, fun y => ?_⟩
  calc
    ‖F x y - F (rep i) y‖ ≤ ‖F x y - centers i y‖ + ‖centers i y - F (rep i) y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε + ε := add_le_add (hi y) (by
      rw [norm_sub_rev]
      exact hrep i ⟨x, hi⟩ y)
    _ = 2 * ε := by ring

theorem exists_uniform_family_member_net_half {X Y I : Type*} [Nonempty X]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε / 2) :
    ∃ rep : I → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ ε := by
  simpa only [mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
    exists_uniform_family_member_net F centers hnet

theorem exists_uniform_family_member_net_with_bounds {X Y I : Type*} [Nonempty X]
    [PseudoMetricSpace Y] (F : X → Y → ℂ) (centers : I → Y → ℂ)
    (K : ℝ≥0) {p ε : ℝ} (hK : (K : ℝ) ≤ Real.exp p)
    (hLip : ∀ x, LipschitzWith K (F x))
    (hunit : ∀ x y, (F x y).im = 0 ∧ 0 ≤ (F x y).re ∧ (F x y).re ≤ 1)
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) :
    ∃ rep : I → X,
      (K : ℝ) ≤ Real.exp p ∧
      (∀ i, LipschitzWith K (F (rep i))) ∧
      (∀ i y, (F (rep i) y).im = 0 ∧ 0 ≤ (F (rep i) y).re ∧
        (F (rep i) y).re ≤ 1) ∧
      ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ 2 * ε := by
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net F centers hnet
  exact ⟨rep, hK, fun i => hLip (rep i), fun i => hunit (rep i), hrep⟩

theorem exists_finite_uniform_family_member_net {X Y : Type*} [Nonempty X]
    (F : X → Y → ℂ) {ε cost : ℝ}
    (hnet : ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
      ∃ centers : Fin n → Y → ℂ, ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp cost ∧
      ∃ rep : Fin n → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ 2 * ε := by
  obtain ⟨n, hn, centers, hcenters⟩ := hnet
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net F centers hcenters
  exact ⟨n, hn, rep, hrep⟩

theorem exists_uniform_family_member_nets_exp_log {X Y : Type*} [Nonempty X]
    (F : X → Y → ℂ) (cost : ℝ → ℝ)
    (hnet : ∀ δ : ℝ, 0 < δ → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp (cost (Real.log (1 / δ))) ∧
      ∃ centers : Fin n → Y → ℂ, ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp (cost (Real.log (2 / ε))) ∧
      ∃ rep : Fin n → X, ∀ x, ∃ i, ∀ y, ‖F x y - F (rep i) y‖ ≤ ε := by
  intro ε hε
  obtain ⟨n, hn, centers, hcenters⟩ := hnet (ε / 2) (by positivity)
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net_half F centers hcenters
  refine ⟨n, ?_, rep, hrep⟩
  have he : 1 / (ε / 2) = 2 / ε := by field_simp
  simpa only [he] using hn

end Erdos3

end

section

namespace Erdos3

theorem uniformFamilyMemberNet_half_log_budget (E : ℕ) {p ε : ℝ}
    (hp : 0 ≤ p) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (p + Real.log (1 / (ε / 2)) + E) ^ E ≤
      (p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2) := by
  have hrecip : 1 ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hlogε : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hrecip
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hratio : 1 / (ε / 2) = (1 / ε) * 2 := by field_simp
  rw [hratio, Real.log_mul (by positivity) (by norm_num)]
  have hbase : 1 ≤ p + Real.log (1 / ε) + (E + 2 : ℕ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) E]
  apply (pow_le_pow_left₀ (by positivity)
    (show p + (Real.log (1 / ε) + Real.log 2) + (E : ℝ) ≤
      p + Real.log (1 / ε) + (E + 2 : ℕ) by push_cast; linarith) E).trans
  exact pow_le_pow_right₀ hbase (by omega)

theorem exists_uniform_family_member_net_of_polynomial_log
    {O Y : Type*} [Nonempty O] (F : O → Y → ℂ) {p : ℝ} (hp : 0 ≤ p) (E : ℕ)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + E) ^ E) ∧
      ∃ centers : Fin n → Y → ℂ, ∀ o, ∃ i, ∀ y, ‖F o y - centers i y‖ ≤ η)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp
      ((p + Real.log (1 / ε) + (E + 2 : ℕ)) ^ (E + 2)) ∧
      ∃ rep : Fin n → O, ∀ o, ∃ i, ∀ y, ‖F o y - F (rep i) y‖ ≤ ε := by
  obtain ⟨n, hn, centers, hcenters⟩ := hnet (ε / 2) (by positivity) (by linarith)
  obtain ⟨rep, hrep⟩ := exists_uniform_family_member_net_half F centers hcenters
  exact ⟨n, hn.trans (Real.exp_le_exp.mpr
    (uniformFamilyMemberNet_half_log_budget E hp hε hε1)), rep, hrep⟩

theorem exists_uniform_family_member_nets_polynomial_log (E : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {O Y : Type*} [Nonempty O] {p : ℝ}, 0 ≤ p →
      ∀ F : O → Y → ℂ,
      (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + E) ^ E) ∧
        ∃ centers : Fin n → Y → ℂ, ∀ o, ∃ i, ∀ y, ‖F o y - centers i y‖ ≤ η) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n : ℕ,
        (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) + C) ^ C) ∧
        ∃ rep : Fin n → O, ∀ o, ∃ i, ∀ y, ‖F o y - F (rep i) y‖ ≤ ε := by
  refine ⟨E + 2, by omega, ?_⟩
  intro O Y inst p hp F hnet ε hε hε1
  exact exists_uniform_family_member_net_of_polynomial_log F hp E hnet ε hε hε1

end Erdos3

end

end OAI
