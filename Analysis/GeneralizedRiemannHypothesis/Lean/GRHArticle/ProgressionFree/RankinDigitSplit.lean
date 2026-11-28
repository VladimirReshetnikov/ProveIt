import GRHArticle.ProgressionFree.Rankin
import GRHArticle.ProgressionFree.RectangularPrefixWeights

/-!
# Separating low and high ternary digits

Passing the Rankin exponent test is equivalent to passing it on each half
of any ternary digit split. A slice at fixed high digits preserves the
absence of three-term arithmetic progressions.
-/

namespace GRHArticle.ProgressionFree

/-- Split a greedy exponent at an arbitrary ternary digit depth. -/
theorem mem_greedyExponents_iff_mod_pow_and_div (n k : ℕ) :
    n ∈ greedyExponents ↔ n % 3^k ∈ greedyExponents ∧ n / 3^k ∈ greedyExponents := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one,zero_mem_greedyExponents]
  | succ k ih =>
    rw [mem_greedyExponents_iff n,mem_greedyExponents_iff (n % 3^(k+1)),pow_succ',
      Nat.mod_mod_of_dvd n (dvd_mul_right 3 (3^k)),Nat.mod_mul_right_div_self,
      ← Nat.div_div_eq_div_mul,ih (n/3),and_assoc]

/-- The Rankin condition can be checked separately in a bounded low block
and on the remaining high digits. -/
theorem mem_greedyExponents_add_pow_mul_iff (a b k : ℕ) (ha : a < 3^k) :
    a + 3^k*b ∈ greedyExponents ↔ a ∈ greedyExponents ∧ b ∈ greedyExponents := by
  rw [mem_greedyExponents_iff_mod_pow_and_div _ k,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha,
    Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt ha,zero_add]

/-- Restrict a rule to a rectangular box after fixing its high ternary digits. -/
def exponentBoxHighSlice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k h : ι → ℕ) (F : Set (ι → ℕ)) : Set (ι → ℕ) :=
  {a | a ∈ exponentBox (fun i ↦ 3^(k i) - 1) ∧ (fun i ↦ a i+3^(k i)*h i) ∈ F}

/-- Translation by the fixed high component preserves progression-freeness. -/
theorem threeAPFree_exponentBoxHighSlice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k h : ι → ℕ) {F : Set (ι → ℕ)} (hF : ThreeAPFree F) :
    ThreeAPFree (exponentBoxHighSlice k h F) := by
  intro a ha b hb c hc he
  have h₁ (i : ι) : a i+c i = b i+b i := congrFun he i
  have he' := hF ha.2 hb.2 hc.2 (by
    funext i
    change (a i+3^(k i)*h i)+(c i+3^(k i)*h i) = (b i+3^(k i)*h i)+(b i+3^(k i)*h i)
    have := h₁ i
    omega)
  funext i
  exact Nat.add_right_cancel (congrFun he' i)

end GRHArticle.ProgressionFree
