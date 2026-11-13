import FreeJHaltModelZero
import DiophantineConsistency.ArithmeticRepunit
import DiophantineConsistency.ArithmeticStandardCasts
import DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle

/-! # P13 converse: residues and Pell sizes

* `2^(2m+1) ≡ 2 (mod 3)`, from `2^(2m) = 3·rep₂(m) + 1`.
* The halt length `N = 581197^(2T+4)` is odd, and `590069·N` is odd too. So
  `q = 2^(590069N) ≡ 2 (mod 3)`. Since `β ≡ 1 (mod 3)`, `J = (q−1)/β ≡ 1`.
* `ψ_b(2) = 2(b+2)`, so `k = 2ψ_B(r+1) ≥ 4(B+2)` once `r ≥ 1`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P72ConvArith
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticRepunit ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exp_two : Exp.exp (2 : V) = 4 := by
  have h := ArithmeticStandardCasts.cast_exp (V := V) 2
  norm_num at h
  exact h

theorem exp_odd_mod_three (m : V) : Exp.exp (2 * m + 1) % 3 = 2 := by
  have h := repunit_identity (V := V) 2 m
  rw [exp_two] at h
  have h3 : (4 : V) - 1 = 3 := by rw [show (4 : V) = 3 + 1 by norm_num, add_tsub_cancel_right]
  rw [h3] at h
  rw [exp_succ, ← h]
  rw [show 2 * (3 * rep 2 m + 1) = 2 + 3 * (2 * rep 2 m) by ring, mod_add_mul' _ _ (by norm_num)]
  exact mod_eq_self_of_lt (by norm_num)

theorem odd_of_mod_two {N : V} (h : N % 2 = 1) : ∃ a : V, N = 2 * a + 1 :=
  ⟨N / 2, by have := div_add_mod N 2; rw [h] at this; exact this.symm⟩

/-- `J ≡ 1 (mod 3)` from `q = 1 + Jβ`, `q ≡ 2` and `β ≡ 1`. -/
theorem J_mod_three (q J β b : V) (hqJ : q = 1 + J * β) (hβ : β = 3 * b + 1)
    (hq : q % 3 = 2) : ∃ j : V, J = 3 * j + 1 := by
  have h1 : (q - 1) % 3 = 1 := by
    have e := div_add_mod q 3
    rw [hq] at e
    set Q3 := q / 3
    have hq' : q = (1 + 3 * Q3) + 1 := by rw [← e]; ring
    have : q - 1 = 1 + 3 * Q3 := by rw [hq', add_tsub_cancel_right]
    rw [this, mod_add_mul' _ _ (by norm_num)]
    exact mod_eq_self_of_lt (by norm_num)
  have h2 : (q - 1) % 3 = J % 3 := by
    have e := div_add_mod J 3
    rw [hqJ, add_tsub_cancel_left, hβ]
    rw [show J * (3 * b + 1) = J % 3 + 3 * (J * b + J / 3) by
      calc J * (3 * b + 1) = 3 * (J * b) + J := by ring
        _ = 3 * (J * b) + (3 * (J / 3) + J % 3) := by rw [e]
        _ = J % 3 + 3 * (J * b + J / 3) := by ring]
    rw [mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (mod_lt _ (by norm_num))]
  refine ⟨J / 3, ?_⟩
  have e := div_add_mod J 3
  rw [← h2, h1] at e
  exact e.symm

theorem y_two (b : V) : ycoord 2 b = 2 * (b + 2) := by
  have hx1 : xcoord 1 b = b + 2 := by simpa using x_succ (0 : V) b
  have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0 : V) b
  have h := y_succ (1 : V) b
  rw [show (1 : V) + 1 = 2 by norm_num, hx1, hy1] at h
  rw [h]; ring

theorem k_large (r B k : V) (hr : 1 ≤ r) (hk : k = 2 * ycoord (r + 1) B) : 4 * (B + 2) ≤ k := by
  have h2 : (2 : V) ≤ r + 1 := by
    simpa [one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr hr
  have hm := (ArithmeticPellCongruences.y_strictMono B).monotone h2
  rw [hk, ← show 2 * (2 * (B + 2)) = 4 * (B + 2) by ring, ← y_two]
  exact mul_le_mul_of_nonneg_left hm (Arithmetic.zero_le _)

end P72ConvArith

#print axioms P72ConvArith.exp_odd_mod_three
#print axioms P72ConvArith.J_mod_three
#print axioms P72ConvArith.y_two
#print axioms P72ConvArith.k_large
