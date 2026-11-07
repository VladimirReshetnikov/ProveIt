import DiophantineConsistency.Adm942.Adm942Kernel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

/-! # The admissible942 kernel modulo the controller modulus

`K ≡ 15862373587 (mod C0)`, `C0 = d·λ = 189269·246929 = 46736004901`: the
residue premise of `Adm942ConstructionUnit.gamma_unit` (the counterpart of
`ArithmeticConstructionKernel.K_cast_common`).

The kernel is never materialized. With selectors at their index, the two
reflected selector bands are one Horner fold of the 942 selector weights in
`ZMod C0` over `WangTiles942.orderedRows`, times `r^1051 + r^2057`
(`selector_reflection`); the 34 label weights are a separate short sum times
`r^1007 + r^2013` (`control_reflection`). Both folds are checked by
`decide +kernel`, and `2^47 mod C0` by `reduce_mod_char`. The residue agrees
with the pinned payload `K.bin.gz` (recomputed from its bytes). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace Adm942KernelResidue
open DiophantineConsistency DiophantineConsistency.WangTiles942
open scoped BigOperators

/-- High-to-low evaluation of the selector weights of a row list. -/
def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × Tile) → R
  | [] => 0
  | a :: l => (selectorWeight a.2 : R) * r ^ l.length + evaluate r l

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) :
    evaluate r l = ∑ j : Fin l.length, (selectorWeight l[j.val].2 : R) * r ^ (l.length - 1 - j.val) := by
  induction l with
  | nil => simp only [evaluate, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
  | cons a l ih =>
      simp only [List.length_cons, evaluate, Fin.sum_univ_succ, Fin.val_zero,
        List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ,
        List.getElem_cons_succ, ih]
      simp only [Nat.sub_sub, Nat.add_comm]

theorem evaluate_ordered {R : Type*} [CommSemiring R] (r : R) :
    evaluate r orderedRows = ∑ i : Fin 942, (selectorWeight (tile i) : R) * r ^ (941 - i.val) := by
  rw [evaluate_sum]
  refine Fintype.sum_equiv (finCongr ordered_count) _ _ (fun j => ?_)
  simp only [finCongr_apply, Fin.val_cast, tile, ordered_count]

/-- Both selector bands, as one fold. -/
theorem selector_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 942, (selectorWeight (tile i) : R) * (r ^ (1992 - i.val) + r ^ (2998 - i.val))) =
      evaluate r orderedRows * (r ^ 1051 + r ^ 2057) := by
  rw [evaluate_ordered, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi := i.isLt
  rw [show 1992 - i.val = (941 - i.val) + 1051 by omega,
    show 2998 - i.val = (941 - i.val) + 2057 by omega, pow_add, pow_add]
  ring

/-- The 34 label entries. -/
abbrev Control := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

/-- The label weights, reflected at `985`. -/
def controlReflection {R : Type*} [CommSemiring R] (r : R) : R :=
  ∑ e : Control, (CurrentKernel2011.weight (.inr e) : R) * r ^ (985 - Adm942Kernel.position (.inr e))

theorem control_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ e : Control, (CurrentKernel2011.weight (.inr e) : R) *
      (r ^ (1992 - Adm942Kernel.position (.inr e)) + r ^ (2998 - Adm942Kernel.position (.inr e)))) =
      controlReflection r * (r ^ 1007 + r ^ 2013) := by
  rw [controlReflection, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have he := Adm942Kernel.position_le (.inr e)
  rw [show 1992 - Adm942Kernel.position (.inr e) = (985 - Adm942Kernel.position (.inr e)) + 1007 by
      omega,
    show 2998 - Adm942Kernel.position (.inr e) = (985 - Adm942Kernel.position (.inr e)) + 2013 by
      omega, pow_add, pow_add]
  ring

/-- The whole kernel over every commutative semiring, for an arbitrary radix. -/
theorem rawWord_cast {R : Type*} [CommSemiring R] (r : ℕ) :
    (Adm942Kernel.rawWord r : R) =
      (r : R) ^ 18 + (r : R) ^ 1005 + (r : R) ^ 4036 +
        (evaluate (r : R) orderedRows * ((r : R) ^ 1051 + (r : R) ^ 2057) +
          controlReflection (r : R) * ((r : R) ^ 1007 + (r : R) ^ 2013)) := by
  rw [Adm942Kernel.rawWord_eq]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Fintype.sum_sum_type, ← selector_reflection, ← control_reflection]
  rfl

/-- The same fold as a linear Horner accumulator. -/
def run {R : Type*} [Semiring R] (r : R) : List (ℕ × Tile) → R → R
  | [], z => z
  | a :: l, z => run r l (z * r + (selectorWeight a.2 : R))

theorem run_eq {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) (z : R) :
    run r l z = z * r ^ l.length + evaluate r l := by
  induction l generalizing z with
  | nil => simp [run, evaluate]
  | cons a l ih =>
    rw [run, ih, evaluate, List.length_cons, pow_succ]
    ring

theorem evaluate_eq_run {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) :
    evaluate r l = run r l 0 := by
  simp only [run_eq, zero_mul, zero_add]

abbrev Modulus : ℕ := 46736004901

private theorem rows_common :
    evaluate (15377598417 : ZMod Modulus) orderedRows = 42689364256 := by
  rw [evaluate_eq_run]
  decide +kernel

private theorem controls_common :
    controlReflection (15377598417 : ZMod Modulus) = 3499410725 := by
  decide +kernel

private theorem radix_common : ((Adm942Kernel.radix : ℕ) : ZMod Modulus) = 15377598417 := by
  change ((2 : ℕ) ^ 47 : ZMod Modulus) = 15377598417
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  reduce_mod_char

theorem K_cast_common : (Adm942Kernel.K : ZMod Modulus) = 15862373587 := by
  rw [Adm942Kernel.K, rawWord_cast, radix_common, rows_common, controls_common]
  reduce_mod_char

attribute [local irreducible] Adm942Kernel.K

theorem K_mod : Adm942Kernel.K % 46736004901 = 15862373587 := by
  have h := congrArg ZMod.val K_cast_common
  have hr : (15862373587 : ZMod Modulus).val = 15862373587 := by decide +kernel
  simpa only [ZMod.val_natCast, hr] using h

end Adm942KernelResidue

#print axioms Adm942KernelResidue.K_cast_common
#print axioms Adm942KernelResidue.K_mod
