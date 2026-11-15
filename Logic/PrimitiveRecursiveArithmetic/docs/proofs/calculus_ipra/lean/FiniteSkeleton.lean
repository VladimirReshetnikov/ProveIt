import Mathlib

/-!
# Finite arithmetic layer for constructive calculus

STATUS: Uncompiled candidate source, written against the ProveIt toolchain
`leanprover/lean4:v4.32.0` / Mathlib `v4.32.0`.  No Lean executable was
available in the preparation environment.  This file deliberately makes no
claim to be a completed or kernel-checked formalization.

These are ambient-Lean lemmas about finite rational arrays.  They are useful
for checking the arithmetic design, but their existence in Lean DOES NOT
establish that the corresponding formula has a derivation in iPRA.
That additional task is to encode rational arrays and the displayed bounded
tests by fixed primitive recursive symbols and explicitly construct
`LeanProofs.ConciseIPRA.Prf PRAAx` derivations with quantifier-free induction.
In particular, a quantified function `Nat → Rat` below is a metatheoretic
parameter, not an object quantified over by first-order iPRA.
-/

namespace ConstructiveCalculus.FiniteCore

def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumQ f n + f n

theorem sumQ_telescope (F : ℕ → ℚ) (n : ℕ) :
    sumQ (fun i => F (i + 1) - F i) n = F n - F 0 := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
      simp only [sumQ, ih]
      ring

theorem sumQ_sub (f g : ℕ → ℚ) (n : ℕ) :
    sumQ (fun i => f i - g i) n = sumQ f n - sumQ g n := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
      simp only [sumQ, ih]
      ring

theorem sumQ_mul (c : ℚ) (f : ℕ → ℚ) (n : ℕ) :
    sumQ (fun i => c * f i) n = c * sumQ f n := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
      simp only [sumQ, ih]
      ring

theorem sumQ_const (c : ℚ) (n : ℕ) :
    sumQ (fun _ => c) n = (n : ℚ) * c := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
      simp only [sumQ, ih, Nat.cast_succ]
      ring

theorem abs_sumQ_le (f : ℕ → ℚ) (n : ℕ) :
    |sumQ f n| ≤ sumQ (fun i => |f i|) n := by
  induction n with
  | zero => simp [sumQ]
  | succ n ih =>
      change |sumQ f n + f n| ≤ sumQ (fun i => |f i|) n + |f n|
      exact (abs_add _ _).trans (add_le_add_right ih _)

theorem sumQ_mono (f g : ℕ → ℚ) (n : ℕ) :
    (∀ i, i < n → f i ≤ g i) → sumQ f n ≤ sumQ g n := by
  induction n with
  | zero => intro h; simp [sumQ]
  | succ n ih =>
      intro h
      change sumQ f n + f n ≤ sumQ g n + g n
      apply add_le_add
      · apply ih
        intro i hi
        exact h i (Nat.lt_trans hi (Nat.lt_succ_self n))
      · exact h n (Nat.lt_succ_self n)

/-- Telescoping propagates local linearization errors to the whole grid. -/
theorem finite_ftc_bound (F f : ℕ → ℚ) (n : ℕ) (h e : ℚ)
    (hlocal : ∀ i, i < n → |F (i + 1) - F i - h * f i| ≤ e) :
    |F n - F 0 - h * sumQ f n| ≤ (n : ℚ) * e := by
  have ident : sumQ (fun i => F (i + 1) - F i - h * f i) n =
      F n - F 0 - h * sumQ f n := by
    rw [sumQ_sub, sumQ_telescope, sumQ_mul]
  rw [← ident]
  calc
    |sumQ (fun i => F (i + 1) - F i - h * f i) n|
        ≤ sumQ (fun i => |F (i + 1) - F i - h * f i|) n := abs_sumQ_le _ _
    _ ≤ sumQ (fun _ => e) n := sumQ_mono _ _ n hlocal
    _ = (n : ℚ) * e := sumQ_const e n

/-! The arithmetic recurrence underlying repeated integration by parts. -/

def alternatingCorrections (C : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => alternatingCorrections C n + (-1 : ℚ) ^ n * C n

theorem finite_parts_chain (C I : ℕ → ℚ) (n : ℕ) :
    (∀ r, r < n → I r = C r - I (r + 1)) →
    I 0 = alternatingCorrections C n + (-1 : ℚ) ^ n * I n := by
  induction n with
  | zero =>
      intro h
      simp [alternatingCorrections]
  | succ n ih =>
      intro h
      have hprev : ∀ r, r < n → I r = C r - I (r + 1) := by
        intro r hr
        exact h r (Nat.lt_trans hr (Nat.lt_succ_self n))
      calc
        I 0 = alternatingCorrections C n + (-1 : ℚ) ^ n * I n := ih hprev
        _ = alternatingCorrections C n + (-1 : ℚ) ^ n * (C n - I (n + 1)) := by
              rw [h n (Nat.lt_succ_self n)]
        _ = alternatingCorrections C (n + 1) + (-1 : ℚ) ^ (n + 1) * I (n + 1) := by
              simp only [alternatingCorrections, pow_succ]
              ring

/-! These structures are specifications of the metatheoretic name layer.
They are not a definition of first-order iPRA or a claim that arbitrary
inhabitants have primitive recursive evaluators.  Concrete instances must
come with fixed PR definitions and object-theory derivations. -/

def eps (k : ℕ) : ℚ := ((2 : ℚ) ^ k)⁻¹

structure RegularName where
  approx : ℕ → ℚ
  coherent : ∀ k l, |approx k - approx l| ≤ eps k + eps l

structure IntervalData where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

/-- A rational approximation interface, with all regularity data explicit.
The exact normalization of the inequalities can be tightened during the
deep embedding; the mathematical manuscript fixes the authoritative one. -/
structure UniformApproximation (A : IntervalData) where
  value : ℚ → ℕ → ℚ
  modulus : ℕ → ℕ
  bound : ℕ
  coherent : ∀ x, A.lo ≤ x → x ≤ A.hi → ∀ k l,
    |value x k - value x l| ≤ eps k + eps l
  bounded : ∀ x, A.lo ≤ x → x ≤ A.hi → ∀ k,
    |value x k| ≤ (bound : ℚ) + eps k
  continuous : ∀ k x y p q,
    A.lo ≤ x → x ≤ A.hi → A.lo ≤ y → y ≤ A.hi →
    |x - y| ≤ eps (modulus k) →
    |value x p - value y q| ≤ eps k + eps p + eps q

end ConstructiveCalculus.FiniteCore
