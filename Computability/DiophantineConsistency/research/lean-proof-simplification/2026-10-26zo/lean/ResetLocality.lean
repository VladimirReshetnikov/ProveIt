import Mathlib.Data.Nat.Basic

/-!
Finite carry normalization between reset fields.
This file proves the arithmetic mechanism only. The ZMod/cell adapter for the
maintained word construction is a proposal, not a checked integration here.
-/
namespace ProofSimplification20261026.ResetLocality

/-- Incoming carry at zero; outgoing carry at each successor field. -/
def run (radix : ℕ) (raw : ℕ → ℕ) (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | i+1 => (raw i + run radix raw seed i) / radix

/-- Only the visited finite prefix needs a carry budget. -/
theorem run_le {radix D L seed : ℕ} (hpos : 0 < radix)
    (raw : ℕ → ℕ) (hseed : seed ≤ D)
    (hbudget : ∀ i < L, raw i + D < (D+1)*radix) :
    ∀ i ≤ L, run radix raw seed i ≤ D := by
  intro i
  induction i with
  | zero => intro _; exact hseed
  | succ i ih =>
      intro hi
      change (raw i + run radix raw seed i) / radix ≤ D
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hpos).mpr
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (ih (by omega)) _) (hbudget i (by omega))

/-- A reset followed by a zero raw field returns every bounded seed to zero. -/
theorem terminal_zero {radix D L seed : ℕ} (hpos : 0 < radix)
    (raw : ℕ → ℕ) (hseed : seed ≤ D)
    (hbudget : ∀ i < L, raw i + D < (D+1)*radix)
    (hreset : raw L + D < radix) (hlast : raw (L+1) = 0) :
    run radix raw seed (L+2) = 0 := by
  have hbound := run_le hpos raw hseed hbudget L (by omega)
  have hz : run radix raw seed (L+1) = 0 :=
    Nat.div_eq_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left hbound _) hreset)
  change (raw (L+1) + run radix raw seed (L+1)) / radix = 0
  rw [hlast, hz, Nat.zero_add, Nat.zero_div]

/-- An existing recurrence is characterized by the finite prefix evaluator. -/
theorem matches_run {radix seed L : ℕ} (raw carries : ℕ → ℕ)
    (hstart : carries 0 = seed)
    (hrec : ∀ i < L, carries (i+1) = (raw i + carries i)/radix) :
    ∀ i ≤ L, carries i = run radix raw seed i := by
  intro i
  induction i with
  | zero => intro _; exact hstart
  | succ i ih =>
      intro hi
      rw [hrec i (by omega), ih (by omega)]
      rfl

/-- Locality: the carry uses only its actual raw prefix and its incoming seed. -/
theorem prefix_congr {radix seed L : ℕ} {raw other : ℕ → ℕ}
    (h : ∀ i < L, raw i = other i) :
    run radix raw seed L = run radix other seed L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      change (raw L + run radix raw seed L)/radix =
        (other L + run radix other seed L)/radix
      rw [h L (by omega), ih (fun i hi => h i (by omega))]

/-- The current cell length is 2011, with reset at 2009 and zero at 2010. -/
theorem current_cell_terminal {seed : ℕ} (raw : ℕ → ℕ) (hseed : seed ≤ 57)
    (hbudget : ∀ i < 2009, raw i + 57 < 58*2^47)
    (hreset : raw 2009 + 57 < 2^47) (hlast : raw 2010 = 0) :
    run (2^47) raw seed 2011 = 0 :=
  terminal_zero (by decide) raw hseed hbudget hreset hlast

/-- Small nontrivial control: a large raw field may create an internal carry. -/
example : run 10 (fun i => if i=0 then 15 else 0) 7 3 = 0 := by decide
example : run 10 (fun i => if i=0 then 15 else 0) 7 1 = 2 := by decide

/-- Without reset, a block can preserve the incoming carry indefinitely. -/
example : run 10 (fun _ => 9) 0 4 = 0 := by decide
example : run 10 (fun _ => 9) 1 4 = 1 := by decide

#print axioms run_le
#print axioms terminal_zero
#print axioms matches_run
#print axioms prefix_congr
#print axioms current_cell_terminal
end ProofSimplification20261026.ResetLocality
