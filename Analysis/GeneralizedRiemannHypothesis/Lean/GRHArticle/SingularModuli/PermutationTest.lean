import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Fin.Basic

/-!
# Permutation test for the power matrix

The mass of the nondiagonal terms with consecutive exponents controls the
nondiagonal terms for every strictly increasing sequence of exponents.
This is the determinant test in Article lemma `smd:lem:perm`.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

private theorem adjustedExponent_of_strictMono {t : ℕ} (e : Fin t → ℕ) (he : StrictMono e) :
    (∀ i : Fin t, (i : ℕ) + (e i - (i : ℕ)) = e i) ∧
      Monotone (fun i : Fin t ↦ e i - (i : ℕ)) := by
  cases t with
  | zero =>
      exact ⟨fun i ↦ i.elim0, fun {i} ↦ i.elim0⟩
  | succ t =>
      have hstep (i : Fin t) : e i.castSucc < e i.succ :=
        (Fin.strictMono_iff_lt_succ.mp he) i
      have hle (i : Fin (t + 1)) : (i : ℕ) ≤ e i := by
        induction i using Fin.induction with
        | zero => exact Nat.zero_le _
        | succ i hi =>
            change (i : ℕ) ≤ e i.castSucc at hi
            change (i : ℕ) + 1 ≤ e i.succ
            have h := hstep i
            omega
      refine ⟨fun i ↦ Nat.add_sub_of_le (hle i), Fin.monotone_iff_le_succ.mpr ?_⟩
      intro i
      change e i.castSucc - (i : ℕ) ≤ e i.succ - ((i : ℕ) + 1)
      have h := hstep i
      omega

private theorem prod_pow_comp_perm_le_prod_pow {t : ℕ} (r : Fin t → ℝ)
    (hr : ∀ i, 0 < r i) (hmono : Monotone r) (w : Fin t → ℕ) (hw : Monotone w)
    (σ : Equiv.Perm (Fin t)) :
    (∏ i, r i ^ w (σ i)) ≤ ∏ i, r i ^ w i := by
  have hlog : Monotone (fun i ↦ Real.log (r i)) :=
    fun i j hij ↦ Real.log_le_log (hr i) (hmono hij)
  have hcast : Monotone (fun i ↦ (w i : ℝ)) := by
    intro i j hij
    change (w i : ℝ) ≤ (w j : ℝ)
    exact_mod_cast hw hij
  have hpos (f : Fin t → ℕ) : (0 : ℝ) < ∏ i, r i ^ f i :=
    Finset.prod_pos fun i _ ↦ pow_pos (hr i) _
  apply (Real.log_le_log_iff (hpos (w ∘ σ)) (hpos w)).mp
  rw [Real.log_prod (fun i _ ↦ pow_ne_zero _ (hr i).ne'),
    Real.log_prod (fun i _ ↦ pow_ne_zero _ (hr i).ne')]
  simpa only [Real.log_pow, Function.comp_apply, mul_comm] using
    (hlog.monovary hcast).sum_mul_comp_perm_le_sum_mul (σ := σ)

/-- The consecutive-exponent permutation mass test proves nonsingularity for
every strictly increasing sequence of natural exponents. -/
theorem det_pow_ne_zero_of_permutation_mass {t : ℕ} (z : Fin t → ℂ)
    (hpos : ∀ i, 0 < ‖z i‖) (hmono : Monotone (fun i ↦ ‖z i‖))
    (hmass : (∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)),
      ∏ i, ‖z i‖ ^ ((σ i : Fin t) : ℕ)) < ∏ i, ‖z i‖ ^ (i : ℕ))
    (e : Fin t → ℕ) (he : StrictMono e) :
    (Matrix.of fun i j : Fin t ↦ z i ^ e j).det ≠ 0 := by
  classical
  let M := Matrix.of fun i j : Fin t ↦ z i ^ e j
  let T (σ : Equiv.Perm (Fin t)) : ℂ :=
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, z i ^ e (σ i)
  have hdet : M.det = ∑ σ, T σ := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  let r (i : Fin t) := ‖z i‖
  let w (i : Fin t) := e i - (i : ℕ)
  obtain ⟨hesum, hw⟩ := adjustedExponent_of_strictMono e he
  let A (σ : Equiv.Perm (Fin t)) := ∏ i, r i ^ ((σ i : Fin t) : ℕ)
  let B := ∏ i, r i ^ w i
  have hnorm (σ : Equiv.Perm (Fin t)) : ‖T σ‖ = ∏ i, r i ^ e (σ i) := by
    have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · simp [h]
      · simp [h]
    simp only [T, r, norm_mul, norm_prod, norm_pow, hsign, one_mul]
  have hfactor (σ : Equiv.Perm (Fin t)) : ‖T σ‖ = A σ * ∏ i, r i ^ w (σ i) := by
    rw [hnorm]
    change (∏ i, r i ^ e (σ i)) = (∏ i, r i ^ ((σ i : Fin t) : ℕ)) * ∏ i, r i ^ w (σ i)
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by rw [← pow_add, hesum]
  have hmax (σ : Equiv.Perm (Fin t)) : ‖T σ‖ ≤ A σ * B := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left (prod_pow_comp_perm_le_prod_pow r hpos hmono w hw σ)
      (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hpos i).le _)
  have hB : 0 < B := Finset.prod_pos fun i _ ↦ pow_pos (hpos i) _
  have hmass' : (∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), A σ) < A 1 := by
    simpa only [A, r, Equiv.Perm.one_apply] using hmass
  have hoff :
      (∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), ‖T σ‖) < ‖T 1‖ := by
    calc
      _ ≤ ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), A σ * B :=
        Finset.sum_le_sum fun σ _ ↦ hmax σ
      _ = (∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), A σ) * B :=
        (Finset.sum_mul ..).symm
      _ < A 1 * B := mul_lt_mul_of_pos_right hmass' hB
      _ = _ := by rw [hfactor]; rfl
  change M.det ≠ 0
  intro h0
  have hsum : (∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin t)), T σ) + T 1 = 0 := by
    rw [Finset.sum_erase_add _ T (Finset.mem_univ (1 : Equiv.Perm (Fin t))), ← hdet, h0]
  have hle := norm_sum_le (Finset.univ.erase (1 : Equiv.Perm (Fin t))) T
  rw [eq_neg_of_add_eq_zero_left hsum, norm_neg] at hle
  exact (not_le_of_gt hoff) hle

end GRHArticle.SingularModuli
