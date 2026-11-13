import DiophantineConsistency.ArithmeticRepunit
import DiophantineConsistency.ArithmeticPow

/-! Extra positive coordinates needed by P65's halt-side witness. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace P65HaltPositiveCoordinates
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticRepunit ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rep_gt_one (d N : V) (hN : 2 ≤ N) : 1 < rep d N := by
  have hn : N = (N - 2) + 1 + 1 := by
    have h := tsub_add_cancel_of_le hN
    calc N = N - 2 + 2 := h.symm
      _ = (N - 2) + 1 + 1 := by ring
  rw [hn, rep_succ, rep_succ]
  have hd : 1 ≤ Exp.exp d := one_le_exp _
  have hr : 1 ≤ rep d (N - 2) * Exp.exp d + 1 :=
    le_add_of_nonneg_left (Arithmetic.zero_le _)
  have hm : 1 ≤ (rep d (N - 2) * Exp.exp d + 1) * Exp.exp d :=
    one_le_mul_of_one_le_of_one_le hr hd
  calc (1 : V) < 1 + 1 := lt_add_one 1
    _ ≤ (rep d (N - 2) * Exp.exp d + 1) * Exp.exp d + 1 :=
      (add_le_add_iff_right 1).mpr hm

theorem rep_index_positive (d N j : V) (hN : 2 ≤ N)
    (hj : rep d N = 3 * j + 1) : 0 < j := by
  have h := rep_gt_one d N hN
  rw [hj] at h
  by_contra hn
  have hz : j = 0 := le_antisymm (le_of_not_gt hn) (Arithmetic.zero_le _)
  simp [hz] at h

theorem halt_length_ge_two (T : V) : 2 ≤ power 581197 ((2*T+3)+1) := by
  have h := power_mono_exponent (581197 : V) 1 ((2*T+3)+1)
    (by norm_num) (by
      calc (1:V) ≤ 3 := by norm_num
        _ ≤ (2*T+3)+1 := by
          exact le_trans (le_add_of_nonneg_left (Arithmetic.zero_le _)) (le_add_of_nonneg_right (Arithmetic.zero_le _)))
  rw [power_one] at h
  exact le_trans (by norm_num) h

theorem shifted_exp_positive (u R q w X : V)
    (hR : 2*u < R) (hq : 0 < q) (hw : w = Exp.exp (R-u))
    (hX : X = q*w) : 0 < X-q := by
  have huR : u + 1 ≤ R := by
    have h : u ≤ 2*u := by
      calc u = 1*u := by simp
        _ ≤ 2*u := mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
    exact le_trans ((add_le_add_iff_right 1).mpr h) (lt_iff_succ_le.mp hR)
  have hex : 1 ≤ R-u := by
    have h := tsub_add_cancel_of_le (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le _)) huR)
    apply (add_le_add_iff_right u).mp
    rw [h]
    simpa [add_comm] using huR
  have hw2 : 2 ≤ w := by
    rw [hw]
    have h := exp_monotone_le.mpr hex
    simpa using h
  have hqx : q < X := by
    rw [hX]
    calc q = q*1 := by simp
      _ < q*w := mul_lt_mul_of_pos_left (lt_of_lt_of_le (by norm_num) hw2) hq
  exact tsub_pos_of_lt hqx

#print axioms P65HaltPositiveCoordinates.rep_index_positive
#print axioms P65HaltPositiveCoordinates.halt_length_ge_two
#print axioms P65HaltPositiveCoordinates.shifted_exp_positive
end P65HaltPositiveCoordinates
