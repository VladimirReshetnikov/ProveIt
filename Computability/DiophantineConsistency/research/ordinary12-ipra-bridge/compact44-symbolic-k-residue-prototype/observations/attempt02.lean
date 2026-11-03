import DiophantineConsistency.CompactSymbolicKernelOpaque
import Mathlib.Tactic.ReduceModChar

/-! Uncompiled draft: verify the symbolic kernel residue by a Horner fold of
the exact 943 Lean rows, without materializing the enormous kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace CompactSymbolicKernelResidue
open CompactSymbolicKernel CompactSymbolicKernelOpaque
open scoped BigOperators

def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ × ℕ × ℕ) → R
  | [] => 0
  | a :: l => (CompactCoefficientMass.selector a : R) * r ^ l.length + evaluate r l

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ × ℕ × ℕ)) :
    evaluate r l = ∑ j : Fin l.length,
      (CompactCoefficientMass.selector l[j.val] : R) * r ^ (l.length - 1 - j.val) := by
  induction l with
  | nil => simp only [evaluate, List.length_nil, Fin.sum_univ_zero]
  | cons a l ih =>
      simp only [List.length_cons, evaluate, Fin.sum_univ_succ, Fin.val_zero,
        List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ,
        List.getElem_cons_succ, ih]
      simp only [Nat.sub_sub, Nat.add_comm]

private theorem evaluate_rows {R : Type*} [CommSemiring R] (r : R) :
    evaluate r Compact943Data.rows = ∑ j : Fin 943,
      (CompactCoefficientMass.selector (Compact943Data.row j) : R) * r ^ (942-j.val) := by
  have h := evaluate_sum r Compact943Data.rows
  have hl := Compact943Data.rows_length
  simp only [Compact943Data.row] at ⊢
  convert h using 1
  simp only [hl]
  rfl

theorem selector_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 943, (CompactCoefficientMass.selector (Compact943Data.row i) : R) *
      (r^(4393-i.val) + r^(5495-i.val))) =
        evaluate r Compact943Data.rows * (r^3451 + r^4553) := by
  rw [evaluate_rows, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.val < 943 := i.isLt
  have h1 : 4393-i.val = (942-i.val)+3451 := by omega
  have h2 : 5495-i.val = (942-i.val)+4553 := by omega
  rw [h1, h2, pow_add, pow_add]
  ring

def run {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ × ℕ × ℕ) → R → R
  | [], z => z
  | a :: l, z => run r l (z * r + (CompactCoefficientMass.selector a : R))

theorem run_eq {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ × ℕ × ℕ)) (z : R) :
    run r l z = z * r ^ l.length + evaluate r l := by
  induction l generalizing z with
  | nil => simp [run, evaluate]
  | cons a l ih =>
    rw [run, ih, evaluate, List.length_cons, pow_succ]
    ring

theorem evaluate_eq_run {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ × ℕ × ℕ)) : evaluate r l = run r l 0 := by
  simp only [run_eq, zero_mul, zero_add]

abbrev Modulus := 342946332593
abbrev Radix := 139640128744

def copyReflection {R : Type*} [CommSemiring R] (r : R) : R :=
  ∑ i : Fin 41, ((2^(10+i.val) : ℕ) : R) *
    (r^(4393-position i) + r^(5495-position i))

private theorem rows_common : evaluate (Radix : ZMod Modulus) Compact943Data.rows =
    294576924025 := by
  rw [evaluate_eq_run]
  decide +kernel

private theorem copies_common : copyReflection (Radix : ZMod Modulus) = 299839741459 := by
  decide +kernel

private theorem rho_common : (rho : ZMod Modulus) = Radix := by
  change (2 : ZMod Modulus)^67 = Radix
  reduce_mod_char

theorem symbolic_kernel_cast : (paramKernel rho : ZMod Modulus) = 284898815895 := by
  rw [paramKernel]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change ((rho : ZMod Modulus)^30 + (rho : ZMod Modulus)^62 +
      (rho : ZMod Modulus)^1100 + (rho : ZMod Modulus)^2201 +
      (∑ i : Fin 943, (CompactCoefficientMass.selector (Compact943Data.row i) : ZMod Modulus) *
        ((rho : ZMod Modulus)^(4393-i.val) + (rho : ZMod Modulus)^(5495-i.val))) +
      copyReflection (rho : ZMod Modulus) + (rho : ZMod Modulus)^8807 *
        (rho : ZMod Modulus)^42) = 284898815895
  rw [selector_reflection, rho_common, rows_common, copies_common]
  reduce_mod_char

theorem symbolic_kernel_mod : paramKernel rho % Modulus = 284898815895 := by
  have h := congrArg ZMod.val symbolic_kernel_cast
  have hr : (284898815895 : ZMod Modulus).val = 284898815895 := by decide +kernel
  simpa only [ZMod.val_natCast, hr] using h

#print axioms symbolic_kernel_cast
#print axioms symbolic_kernel_mod
end CompactSymbolicKernelResidue
