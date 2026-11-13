import DiophantineConsistency.Mixed121.Mixed121Kernel
import Mathlib.Tactic.ReduceModChar

/-! # The 121x8801 kernel modulo the controller modulus

`paramKernel (2^121) ≡ 510020909 (mod C0)`, where `C0 = d·λ = 2492980061`.
This is the residue premise of `Mixed121ConstructionUnit.gamma_unit`.

The kernel is never materialized. The 943 clause coefficients are folded by
Horner's rule in `ZMod C0` (`rows_common`), using the reflection identity
`Σ clause(i)·(r^(4393−i) + r^(5495−i)) = evaluate r rows · (r^3451 + r^4553)`.
The 44 copy and anchor weights are a separate sum (`copies_common`). Both
are checked by `decide +kernel`; `2^121 mod C0` is checked by
`reduce_mod_char`. This is the design of Compact44's `SymbolicKernelResidue`,
with the 121x8801 clause coefficients and offsets `2200` and `8801`.

The residue agrees with the pinned payload `K.bin` of package 31: its value
modulo `C0` is `510020909`, recomputed from the payload bytes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace Mixed121KernelResidue
open Mixed121Kernel
open scoped BigOperators

def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × ℕ × ℕ × ℕ) → R
  | [] => 0
  | a :: l => (clause a : R) * r ^ l.length + evaluate r l

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R)
    (l : List (ℕ × ℕ × ℕ × ℕ)) :
    evaluate r l = ∑ j : Fin l.length, (clause l[j.val] : R) * r ^ (l.length - 1 - j.val) := by
  induction l with
  | nil => simp only [evaluate, List.length_nil, Fin.sum_univ_zero]
  | cons a l ih =>
      simp only [List.length_cons, evaluate, Fin.sum_univ_succ, Fin.val_zero,
        List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ,
        List.getElem_cons_succ, ih]
      simp only [Nat.sub_sub, Nat.add_comm]

private theorem evaluate_rows {R : Type*} [CommSemiring R] (r : R) :
    evaluate r Compact943Data.rows = ∑ j : Fin 943,
      (clause (Compact943Data.row j) : R) * r ^ (942-j.val) := by
  have h := evaluate_sum r Compact943Data.rows
  have hl := Compact943Data.rows_length
  simp only [Compact943Data.row] at ⊢
  convert h using 1
  simp only [hl]
  rfl

theorem clause_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 943, (clause (Compact943Data.row i) : R) * (r^(4393-i.val) + r^(5495-i.val))) =
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
  | a :: l, z => run r l (z * r + (clause a : R))

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

abbrev Modulus := 2492980061
abbrev Radix := 2465805630

def copyReflection {R : Type*} [CommSemiring R] (r : R) : R :=
  ∑ k : Fin 44, ((W k.val : ℕ) : R) * (r^(4393-extraPos k) + r^(5495-extraPos k))

private theorem rows_common : evaluate (Radix : ZMod Modulus) Compact943Data.rows =
    2093779003 := by
  rw [evaluate_eq_run]
  decide +kernel

private theorem copies_common : copyReflection (Radix : ZMod Modulus) = 232032576 := by
  decide +kernel

private theorem rho_common : (rho : ZMod Modulus) = Radix := by
  change (2 : ZMod Modulus)^121 = Radix
  reduce_mod_char

theorem kernel_cast : (paramKernel rho : ZMod Modulus) = 510020909 := by
  rw [paramKernel]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  change ((rho : ZMod Modulus)^30 + (rho : ZMod Modulus)^62 +
      (rho : ZMod Modulus)^1100 + (rho : ZMod Modulus)^2200 +
      (∑ i : Fin 943, (clause (Compact943Data.row i) : ZMod Modulus) *
        ((rho : ZMod Modulus)^(4393-i.val) + (rho : ZMod Modulus)^(5495-i.val))) +
      copyReflection (rho : ZMod Modulus) + (rho : ZMod Modulus)^8801 *
        (rho : ZMod Modulus)^42) = 510020909
  rw [clause_reflection, rho_common, rows_common, copies_common]
  reduce_mod_char

theorem kernel_mod : paramKernel rho % Modulus = 510020909 := by
  have h := congrArg ZMod.val kernel_cast
  have hr : (510020909 : ZMod Modulus).val = 510020909 := by decide +kernel
  simpa only [ZMod.val_natCast, hr] using h

#print axioms kernel_cast
#print axioms kernel_mod
end Mixed121KernelResidue
