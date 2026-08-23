import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Multiplicative independence of the terminal factorials

For a mesoscopic pair `1 < M < A` put `F t = (A^t)! / (A^t - M^t)! = (A^t).descFactorial (M^t)`,
the terminal falling factorial governing the factorial-cocycle framework.  If a prime `p` lies
in the terminal window `(A^t - M^t, A^t]` — such a prime exists for every large `t` by
Baker–Harman–Pintz, since the window has length `(A^t)^α` with `α = log M / log A > 0.525` —
then

* `v_p (F t) = 1` (exactly one multiple of `p` in the window, and `p² > A^t`), and
* `p ∤ F t'` for every `t' < t` (all factors of `F t'` are at most `A^{t'} < p`).

Consequently the family `F n₀, F n₀+1, F n₀+2, …` is *multiplicatively independent*: a
relation `∏ⱼ F(n₀+j)^{c_j} = 1` in `ℚ` with integer exponents forces every `c_j = 0`, by
downward induction on the top nonzero exponent.  In particular no factorial cocycle
`𝓕_{P,n}` with nonzero exponent polynomial can equal `1` exactly.

The prime-existence input is kept as an explicit hypothesis (`hwin`); everything else is
elementary and kernel-checked.  This file proves the valuation lemmas and the independence
theorem in a range-uniform form.
-/

namespace LeanProofs.TwoBaseIntegerExponent.TerminalFactorial

open Finset

/-- The terminal falling factorial `F t = A^t (A^t - 1) ⋯ (A^t - M^t + 1)`. -/
def termFall (A M t : ℕ) : ℕ := (A ^ t).descFactorial (M ^ t)

theorem termFall_pos {A M : ℕ} (hMA : M ≤ A) (t : ℕ) : 0 < termFall A M t := by
  unfold termFall
  rw [Nat.pos_iff_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt, not_lt]
  exact Nat.pow_le_pow_left hMA t

/-- A window prime has valuation exactly one in the terminal factorial:
if `A^t - M^t < p ≤ A^t`, `2 * (A^t - M^t) ≥ A^t` (so a second multiple does not fit) and
`p^2 > A^t`, then `v_p (F t) = 1`. -/
theorem padicValNat_termFall_eq_one {A M t p : ℕ} [hp : Fact p.Prime]
    (hMA : M ≤ A) (hlo : A ^ t - M ^ t < p) (hhi : p ≤ A ^ t)
    (hhalf : A ^ t ≤ 2 * (A ^ t - M ^ t)) (hsq : A ^ t < p ^ 2) :
    padicValNat p (termFall A M t) = 1 := by
  have hMt : M ^ t ≤ A ^ t := Nat.pow_le_pow_left hMA t
  have hfac := Nat.factorial_mul_descFactorial hMt
  -- `v_p (A^t !) = v_p ((A^t - M^t)!) + v_p (F t)`
  have hlog : Nat.log p (A ^ t) < 2 := by
    by_contra hle
    rw [not_lt] at hle
    have h1 := Nat.pow_log_le_self p (show A ^ t ≠ 0 by omega)
    have h2 : p ^ 2 ≤ p ^ Nat.log p (A ^ t) := Nat.pow_le_pow_right hp.out.pos hle
    omega
  have hv : padicValNat p (Nat.factorial (A ^ t)) = A ^ t / p := by
    rw [padicValNat_factorial (b := 2) hlog]
    simp
  have hvlow : padicValNat p (Nat.factorial (A ^ t - M ^ t)) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [Nat.Prime.dvd_factorial hp.out]
    omega
  have hone : A ^ t / p = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  have hF : 0 < termFall A M t := termFall_pos hMA t
  have hmul : padicValNat p (Nat.factorial (A ^ t - M ^ t)) + padicValNat p (termFall A M t)
      = padicValNat p (Nat.factorial (A ^ t)) := by
    rw [← padicValNat.mul (Nat.factorial_pos _).ne' hF.ne']
    unfold termFall
    rw [hfac]
  omega

/-- A prime exceeding `A^{t'}` does not divide the terminal factorial at level `t'`. -/
theorem not_dvd_termFall_of_lt {A M t' p : ℕ} (hp : p.Prime) (hMA : M ≤ A)
    (h : A ^ t' < p) : ¬ p ∣ termFall A M t' := by
  intro hdvd
  unfold termFall at hdvd
  have hMt : M ^ t' ≤ A ^ t' := Nat.pow_le_pow_left hMA t'
  have hdf : p ∣ Nat.factorial (A ^ t') := by
    rw [← Nat.factorial_mul_descFactorial hMt]
    exact Dvd.dvd.mul_left hdvd _
  rw [Nat.Prime.dvd_factorial hp] at hdf
  omega

/-- Valuation of a finite product of nonzero rationals. -/
theorem padicValRat_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- **Multiplicative independence of the terminal factorials.**  Suppose that for every level
`j ≤ d` there is a prime `p j` in the terminal window at level `n₀ + j` (with the elementary
side conditions).  Then integer exponents `c` with `∏ j ≤ d, F (n₀+j) ^ (c j) = 1` in `ℚ` all
vanish. -/
theorem termFall_multiplicative_independent {A M n₀ d : ℕ} (hM2 : 2 ≤ M) (hAM : M ≤ A)
    (p : ℕ → ℕ) (hp : ∀ j ≤ d, (p j).Prime)
    (hwin : ∀ j ≤ d,
      A ^ (n₀ + j) - M ^ (n₀ + j) < p j ∧ p j ≤ A ^ (n₀ + j) ∧
      A ^ (n₀ + j) ≤ 2 * (A ^ (n₀ + j) - M ^ (n₀ + j)) ∧ A ^ (n₀ + j) < p j ^ 2)
    (c : ℕ → ℤ)
    (hrel : ∏ j ∈ range (d + 1), ((termFall A M (n₀ + j) : ℚ)) ^ (c j) = 1) :
    ∀ j ≤ d, c j = 0 := by
  classical
  -- Strong downward induction on the top index with nonzero exponent.
  by_contra hcon
  rw [not_forall] at hcon
  obtain ⟨j₀, hj₀⟩ := hcon
  rw [Classical.not_imp] at hj₀
  obtain ⟨hj₀d, hj₀⟩ := hj₀
  -- take the largest bad index
  have hex : ((range (d + 1)).filter (fun j => c j ≠ 0)).Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj₀⟩⟩
  set jm := ((range (d + 1)).filter (fun j => c j ≠ 0)).max' hex with hjm
  have hjm_mem := ((range (d + 1)).filter (fun j => c j ≠ 0)).max'_mem hex
  rw [Finset.mem_filter, Finset.mem_range] at hjm_mem
  obtain ⟨hjmd, hcjm⟩ := hjm_mem
  have hjmd' : jm ≤ d := by omega
  haveI := Fact.mk (hp jm hjmd')
  obtain ⟨hlo, hhi, hhalf, hsq⟩ := hwin jm hjmd'
  -- apply `v_{p jm}` to the relation
  have hvrel := congrArg (padicValRat (p jm)) hrel
  rw [padicValRat.one] at hvrel
  have hF0 : ∀ j, ((termFall A M (n₀ + j) : ℚ)) ≠ 0 := fun j => by
    exact_mod_cast (termFall_pos hAM (n₀ + j)).ne'
  rw [padicValRat_prod _ _ (fun j _ => zpow_ne_zero _ (hF0 j))] at hvrel
  have hterm : ∀ j ∈ range (d + 1),
      padicValRat (p jm) (((termFall A M (n₀ + j) : ℚ)) ^ (c j))
        = c j * padicValRat (p jm) ((termFall A M (n₀ + j) : ℚ)) := fun j _ =>
    padicValRat.zpow _
  rw [Finset.sum_congr rfl hterm] at hvrel
  -- each summand: 0 for j > jm (c j = 0), 0 for j < jm (prime too large), c jm for j = jm
  have hsplit : ∀ j ∈ range (d + 1), c j * padicValRat (p jm) ((termFall A M (n₀ + j) : ℚ))
      = if j = jm then c jm else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_trichotomy j jm with hlt | heq | hgt
    · -- prime exceeds A^{n₀+j}
      have hAj : A ^ (n₀ + j) < p jm := by
        have h1 : A ^ (n₀ + j) ≤ A ^ (n₀ + jm - 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : 2 * A ^ (n₀ + jm - 1) ≤ A ^ (n₀ + jm) := by
          have he : A ^ (n₀ + jm) = A * A ^ (n₀ + jm - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          rw [he]
          exact Nat.mul_le_mul_right _ (by omega)
        omega
      have hnd := not_dvd_termFall_of_lt (hp jm hjmd') hAM hAj
      have : padicValRat (p jm) ((termFall A M (n₀ + j) : ℚ)) = 0 := by
        rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
        simp
      rw [this, mul_zero, if_neg (by omega)]
    · rw [if_pos heq, heq]
      have h1 : padicValRat (p jm) ((termFall A M (n₀ + jm) : ℚ)) = 1 := by
        rw [padicValRat.of_nat, padicValNat_termFall_eq_one hAM hlo hhi hhalf hsq]
        simp
      rw [h1, mul_one]
    · -- j > jm: c j = 0 by maximality
      have : c j = 0 := by
        by_contra hne
        have : j ∈ (range (d + 1)).filter (fun j => c j ≠ 0) := by
          rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, hne⟩
        have := Finset.le_max' _ _ this
        omega
      rw [this, zero_mul, if_neg (by omega)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_eq' (range (d + 1)) jm,
    if_pos (Finset.mem_range.mpr (by omega))] at hvrel
  exact hcjm hvrel

end LeanProofs.TwoBaseIntegerExponent.TerminalFactorial
