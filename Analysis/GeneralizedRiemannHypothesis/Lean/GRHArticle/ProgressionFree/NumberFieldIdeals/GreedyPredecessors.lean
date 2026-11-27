import GRHArticle.ProgressionFree.Rankin
import Mathlib.Data.Finset.Card

/-!
# Greedy predecessors and the pure-power exchange

The two predecessors of a ternary exponent keep the digits `1` and the
nonzero digits, respectively. The resulting exponents have only binary
ternary digits.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

/-- Every exponent is the last term of a weak progression whose first two
terms are greedy. The inequalities become strict for a nongreedy exponent. -/
theorem exists_greedyPredecessors (m : ℕ) :
    ∃ a b : ℕ, a ∈ greedyExponents ∧ b ∈ greedyExponents ∧
      a ≤ b ∧ b ≤ m ∧ a + m = b + b ∧ (m ∉ greedyExponents → a < b ∧ b < m) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hzero : m = 0
    · subst m
      exact ⟨0, 0, zero_mem_greedyExponents, zero_mem_greedyExponents,
        le_rfl, le_rfl, rfl, fun h ↦ (h zero_mem_greedyExponents).elim⟩
    obtain ⟨a, b, ha, hb, hab, _, he, _⟩ :=
      ih (m / 3) (Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide))
    let u : ℕ := if m % 3 = 1 then 1 else 0
    let v : ℕ := if m % 3 = 0 then 0 else 1
    have hd : u ≤ v ∧ v ≤ 1 ∧ u + m % 3 = v + v := by
      dsimp [u, v]
      split_ifs <;> omega
    have ha' : 3*a + u ∈ greedyExponents := by
      rw [mem_greedyExponents_iff]
      refine ⟨by omega, ?_⟩
      rwa [show (3*a + u) / 3 = a by omega]
    have hb' : 3*b + v ∈ greedyExponents := by
      rw [mem_greedyExponents_iff]
      refine ⟨by omega, ?_⟩
      rwa [show (3*b + v) / 3 = b by omega]
    have hab' : 3*a + u ≤ 3*b + v := by omega
    have he' : (3*a + u) + m = (3*b + v) + (3*b + v) := by omega
    refine ⟨3*a + u, 3*b + v, ha', hb', hab', by omega, he', fun h ↦ ?_⟩
    by_contra! hn
    exact h ((show 3*a + u = m by omega) ▸ ha')

/-- The pure-prime exponents in the modified set through exponent eight. -/
def exchangedExponents : Finset ℕ := {0, 1, 3, 7, 8}

private theorem small_greedy_digits : ∀ n : Fin 9,
    (∀ d ∈ Nat.digits 3 n.val, d ≤ 1) ↔ n.val ∈ ({0, 1, 3, 4} : Finset ℕ) := by
  decide +kernel

theorem mem_greedyExponents_of_le_eight {n : ℕ} (hn : n ≤ 8) :
    n ∈ greedyExponents ↔ n ∈ ({0, 1, 3, 4} : Finset ℕ) :=
  small_greedy_digits ⟨n, by omega⟩

private theorem exchangedExponents_test : ∀ a b c : Fin 9,
    a.val ∈ exchangedExponents → b.val ∈ exchangedExponents → c.val ∈ exchangedExponents →
      a.val + c.val = b.val + b.val → a.val = b.val := by
  decide +kernel

/-- The five modified pure powers exclude every nonconstant progression. -/
theorem threeAPFree_exchangedExponents : ThreeAPFree (exchangedExponents : Set ℕ) := by
  intro a ha b hb c hc h
  have maxExponent : ∀ {e}, e ∈ exchangedExponents → e < 9 := by
    intro e he
    simp [exchangedExponents] at he
    omega
  exact exchangedExponents_test ⟨a, maxExponent ha⟩ ⟨b, maxExponent hb⟩
    ⟨c, maxExponent hc⟩ ha hb hc h

end GRHArticle.ProgressionFree.NumberFieldIdeals
