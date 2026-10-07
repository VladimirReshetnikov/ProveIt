import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped fwdDiff

theorem norm_fwdDiff_iter_le_local {V : Type*} [SeminormedAddCommGroup V]
    (f : ℕ → V) (n x : ℕ) {ε : ℝ}
    (h : ∀ k ≤ n, ‖f (x + k)‖ ≤ ε) : ‖Δ_[1]^[n] f x‖ ≤ (2 : ℝ) ^ n * ε := by
  induction n generalizing x with
  | zero => simpa using h 0 (by omega)
  | succ n ih =>
    have hleft : ‖Δ_[1]^[n] f (x + 1)‖ ≤ (2 : ℝ) ^ n * ε := by
      apply ih
      intro k hk
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (k + 1) (by omega)
    have hright : ‖Δ_[1]^[n] f x‖ ≤ (2 : ℝ) ^ n * ε :=
      ih x (fun k hk => h k (by omega))
    rw [Function.iterate_succ_apply']
    change ‖Δ_[1]^[n] f (x + 1) - Δ_[1]^[n] f x‖ ≤ _
    exact (norm_sub_le _ _).trans (by rw [pow_succ]; linarith)

theorem fwdDiff_iter_sub {V : Type*} [AddCommGroup V]
    (f g : ℕ → V) (n x : ℕ) :
    Δ_[1]^[n] (fun k => f k - g k) x = Δ_[1]^[n] f x - Δ_[1]^[n] g x := by
  simp only [fwdDiff_iter_eq_sum_shift, smul_sub, Finset.sum_sub_distrib]

theorem fwdDiff_iter_intCast (g : ℕ → ℤ) (n x : ℕ) :
    Δ_[1]^[n] (fun k => (g k : ℝ)) x = (Δ_[1]^[n] g x : ℤ) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', fwdDiff, ih, Int.cast_sub]

theorem fwdDiff_iter_natCast (f : ℝ → ℝ) (n x : ℕ) :
    Δ_[1]^[n] (fun k : ℕ => f k) x = Δ_[(1 : ℝ)]^[n] f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', fwdDiff, ih, Nat.cast_add, Nat.cast_one]

theorem integer_fwdDiff_eq_zero_of_close (g : ℕ → ℤ) (f : ℕ → ℝ) (n x : ℕ)
    {ε : ℝ} (hsmall : (2 : ℝ) ^ n * ε < 1)
    (happrox : ∀ k ≤ n, ‖(g (x + k) : ℝ) - f (x + k)‖ ≤ ε)
    (hf : Δ_[1]^[n] f x = 0) : Δ_[1]^[n] g x = 0 := by
  have hbound := norm_fwdDiff_iter_le_local (fun k => (g k : ℝ) - f k) n x happrox
  rw [fwdDiff_iter_sub, fwdDiff_iter_intCast, hf, sub_zero] at hbound
  have habs : |((Δ_[1]^[n] g x : ℤ) : ℝ)| < 1 := by
    simpa only [Real.norm_eq_abs] using hbound.trans_lt hsmall
  have hleft : (-1 : ℤ) < Δ_[1]^[n] g x := by exact_mod_cast (abs_lt.mp habs).1
  have hright : Δ_[1]^[n] g x < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  omega

theorem integer_polynomial_lift_differences (P : Polynomial ℝ) (g : ℕ → ℤ)
    {s N : ℕ} {ε : ℝ} (hdegree : P.natDegree ≤ s)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - P.eval (n : ℝ)‖ ≤ ε) :
    ∀ x, x + s + 1 < N → Δ_[1]^[s + 1] g x = 0 := by
  intro x hx
  apply integer_fwdDiff_eq_zero_of_close g (fun n => P.eval n) (s + 1) x hsmall
  · intro k hk
    exact happrox (x + k) (by omega)
  · rw [fwdDiff_iter_natCast P.eval]
    have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) (by omega : P.natDegree < s + 1)
    exact congrFun hzero (x : ℝ)

end Erdos3

end

end OAI
