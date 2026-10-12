import GowersSzemeredi.Proofs18CoverExponents
import GowersSzemeredi.Proofs18GenericLengths

/-! Shared class budgets and elementary estimates for the uniform cover step.
The polynomial and final-threshold arguments use the same budget inputs. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The tight log-log bound of the class base. -/
def tightMuV (k : Nat) : Nat := 2 ^ (k + 4) + 1

/-- The tight base budget. -/
def tightMu0 (k : Nat) : Nat := max (tightMuV k) (fixDeg k) + 2

/-- **The class base is at most `2^(2^(2^(k+4)+1))`.** -/
theorem classV_le_tight (Kc pc : Nat → Nat)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) (k : Nat) :
    classV Kc pc k ≤ 2 ^ (2 ^ tightMuV k) := by
  set E := (2 : Nat) ^ ((2 : Nat) ^ (k + 4)) with hE
  have hterm : ∀ j ∈ Finset.range k, (Kc j : Real) + pc j ≤ 2 ^ E := by
    intro j hj
    have hjk : j + 5 ≤ k + 4 := by have := Finset.mem_range.mp hj; omega
    refine (hconst j).trans (pow_le_pow_right₀ (by norm_num) ?_)
    exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hjk)
  have hsum : ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) ≤ k * 2 ^ E := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hk1 : ((k : Real) + 1) ≤ 2 ^ (k + 1) := by
    have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    exact_mod_cast h.le
  have hkE : k + 1 + E ≤ 2 ^ tightMuV k := by
    have h1 : k + 4 < 2 ^ (k + 4) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k + 4) < E := Nat.lt_two_pow_self
    have h3 : 2 ^ tightMuV k = 2 * E := by
      unfold tightMuV; rw [pow_succ, hE]; ring
    omega
  calc classV Kc pc k ≤ ((k : Real) + 1) * 2 ^ E := by
        unfold classV
        nlinarith
    _ ≤ 2 ^ (k + 1) * 2 ^ E := mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ = 2 ^ (k + 1 + E) := by rw [pow_add (2 : Real) (k + 1) E]
    _ ≤ 2 ^ (2 ^ tightMuV k) := pow_le_pow_right₀ (by norm_num) hkE

/-- The standing hypotheses at the tight base budget. -/
theorem tightHyp_of_profiles (Kc pc : Nat → Nat) (hK : ∀ k, 2 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5)))) {k : Nat}
    (hk : 2 ≤ k) :
    (⟨classV Kc pc k, k, Kc k, pc k, tightMu0 k⟩ : GenParamsC).CHyp (tightMuV k) (genMuK k) := by
  obtain ⟨hV, -, -, -, -, -, hKk, hKμ, hpk, hpμ⟩ := stdHyp_of_profiles Kc pc hK hp hconst hk
  refine ⟨hV, classV_le_tight Kc pc hconst k, le_rfl, ?_, hKk, hKμ, hpk, hpμ⟩
  show k ≤ 2 ^ tightMu0 k
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ 2 ^ tightMu0 k := Nat.pow_le_pow_right (by norm_num) (by
        unfold tightMu0 fixDeg; have := Nat.lt_two_pow_self (n := k + 5)
        have := le_max_right (tightMuV k) (2 ^ (k + 5) + 7); omega)

theorem two_pow_six_mul (k : Nat) : 2 ^ (k + 6) = 64 * 2 ^ k := by rw [pow_add]; ring
theorem two_pow_five_mul (k : Nat) : 2 ^ (k + 5) = 32 * 2 ^ k := by rw [pow_add]; ring

theorem two_pow_four_mul (k : Nat) : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring

/-- `(k+3)³ ≤ 32·2^k`. -/
theorem cube_le_two_pow_sharp (k : Nat) : (k + 3) ^ 3 ≤ 32 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; norm_num
    · have hstep : (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := by
        have hk : 1 ≤ k := h
        nlinarith [sq_nonneg (k : Nat), hk]
      calc (k + 1 + 3) ^ 3 ≤ 2 * (k + 3) ^ 3 := hstep
        _ ≤ 2 * (32 * 2 ^ k) := Nat.mul_le_mul_left _ ih
        _ = 32 * 2 ^ (k + 1) := by rw [pow_succ]; ring

/-- `(k+4)² ≤ 4·2^k` for `k ≥ 4`. -/
theorem sq_le_two_pow_four : ∀ k, 4 ≤ k → (k + 4) ^ 2 ≤ 4 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hstep : (k + 1 + 4) ^ 2 ≤ 2 * (k + 4) ^ 2 := by nlinarith
    calc (k + 1 + 4) ^ 2 ≤ 2 * (k + 4) ^ 2 := hstep
      _ ≤ 2 * (4 * 2 ^ k) := Nat.mul_le_mul_left _ ih
      _ = 4 * 2 ^ (k + 1) := by rw [pow_succ]; ring

end LeanProofs.GowersSzemeredi
