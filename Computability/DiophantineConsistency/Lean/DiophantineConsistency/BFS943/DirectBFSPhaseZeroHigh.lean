import DiophantineConsistency.BFS943.DirectBFSKernelDivisibility
import DiophantineConsistency.BFS943.DirectBFSKernelBlockSize
import DiophantineConsistency.BFS943.DirectBFSPackedCell
import DiophantineConsistency.BFS943.DirectBFSCellLowMask
import DiophantineConsistency.Compact44.HighMaskLocal

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSPhaseZeroHigh
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticStandardCasts ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPackingBlocks
  ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel DirectBFSSymbolicKernel CompactSymbolicPorts
open DirectBFSKernelDivisibility DirectBFSKernelBlockSize DirectBFSPackedCell DirectBFSCellDigit DirectBFSCellSizeBound
  DirectBFSUniformPackedCell
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eight_dvd_exp {e : V} (he : 3 ≤ e) : (8 : V) ∣ Exp.exp e := by
  obtain ⟨d, rfl⟩ := exists_add_of_le he
  refine ⟨Exp.exp d, ?_⟩
  rw [add_comm, show d+3=d+1+1+1 by ring, exp_succ, exp_succ, exp_succ]
  ring

theorem kernel_dvd_eight : (8 : V) ∣ (paramKernel rho : V) := by
  have hr : 8 ∣ rho := by unfold rho; norm_num
  have hn : 8 ∣ paramKernel rho :=
    dvd_trans hr (DirectBFSKernelDivisibility.radix_dvd rho)
  have h := cast_mod (V:=V) (paramKernel rho) 8
  rw [Nat.mod_eq_zero_of_dvd hn] at h
  apply mod_eq_zero_iff_dvd.mp
  simpa using h.symm

/-- A compact cell has only its Boolean selector-zero bit below bit 67. -/
theorem cell_mod_eight (a d : V) (hd : d ≤ 1) : packedCell a d % 8 ≤ 1 := by
  have hs := packedCell_digit a d 0 hd (by norm_num)
  rw [dig_zero_index] at hs
  have hb : packedCell a d % Exp.exp 67 ≤ 1 := by
    rw [hs]
    exact cellDigit_le_one a d 0 hd
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤67)) (packedCell a d)
  rw [mod_eq_self_of_lt (lt_of_le_of_lt hb (by norm_num))] at hm
  rw [← hm]
  exact hb

theorem low_dvd_eight (x : V) : (8:V) ∣ ((paramKernel rho : V)*x % Exp.exp 590069) := by
  have hp : (8:V) ∣ (paramKernel rho : V)*x := dvd_mul_of_dvd_left kernel_dvd_eight _
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤590069)) ((paramKernel rho : V)*x)
  apply mod_eq_zero_iff_dvd.mp
  rw [hm, mod_eq_zero_iff_dvd.mpr hp]

theorem high_dvd_eight (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    (8:V) ∣ ((paramKernel rho : V)*x / Exp.exp 590069) := by
  rw [high_product x hx]
  exact dvd_mul_of_dvd_left (eight_dvd_exp (by norm_num : (3:V)≤67*42)) _

/-- A number congruent to zero or one modulo eight cannot overlap bit two. -/
theorem noCarry_four_of_mod_eight (x : V) (hx : x % 8 ≤ 1) : NoCarry x 4 := by
  have h8 : Exp.exp (3:V) = 8 := by simpa using cast_exp (V:=V) 3
  have hl : NoCarry (x % 8) (4:V) := by
    rcases le_one_iff_eq_zero_or_one.mp hx with hz | ho
    · rw [hz, noCarry_iff]; intro i; simp
    · rw [ho]
      apply DirectBFSBaseLowNoCarry.one_noCarry_even
      apply mod_eq_zero_iff_dvd.mpr
      exact ⟨2, by norm_num⟩
  have hh : NoCarry (x / 8) (0:V) := by rw [noCarry_iff]; intro i; simp
  have ha : x%8 < Exp.exp (3:V) := by rw [h8]; exact mod_lt _ (by norm_num)
  have hb : (4:V) < Exp.exp 3 := by rw [h8]; norm_num
  have h := noCarry_concat ha hb hl hh
  have he : (x/8)*Exp.exp (3:V) + x%8 = x := by
    rw [h8, mul_comm]; exact div_add_mod x 8
  rw [he] at h
  simpa only [zero_mul, zero_add] using h

/-- Every physical compact block has no carry at high-mask phase zero. -/
theorem phase_zero_noCarry {row dummy : V → V} {N s j : V}
    (hw : DirectBFSLocalWord.Word row N s) :
    NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) j) 0) (dig 67 (highNat : V) 0) := by
  let X : V → V := fun k => normalizedCell (row k) (dummy k)
  have hk : cyc N j 1 < N := cyc_lt hw.pos j 1
  have hd (k : V) : dummy k % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt _ (by norm_num))
  have hsmall : X (cyc N j 1) < Exp.exp (67*3297+1 : V) := by
    exact lt_of_lt_of_le (packedCell_lt_support (row (cyc N j 1)) (dummy (cyc N j 1)%2)
      (hw.tile_ne _ hk) (hd _)) (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hlo : (8:V) ∣ lo 590069 (paramKernel rho : V) X j := low_dvd_eight _
  have hhi : (8:V) ∣ hi 590069 (paramKernel rho : V) X (cyc N j 1) := high_dvd_eight _ hsmall
  have hsum : (blk 590069 (paramKernel rho : V) N s X j) % 8 ≤ 1 := by
    change (lo 590069 (paramKernel rho : V) X j +
      hi 590069 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) % 8 ≤ 1
    rw [mod_add_remove_left_of_dvd (dvd_add hlo hhi) (by norm_num)]
    exact cell_mod_eight (row (cyc N j s)) (dummy (cyc N j s)%2) (hd _)
  have hm := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<8)
    (eight_dvd_exp (by norm_num : (3:V)≤67)) (blk 590069 (paramKernel rho : V) N s X j)
  have hdigit : (dig 67 (blk 590069 (paramKernel rho : V) N s X j) 0) % 8 ≤ 1 := by
    rw [dig_zero_index, hm]
    exact hsum
  rw [HighMaskLocal.origin]
  exact noCarry_four_of_mod_eight _ hdigit

#print axioms DirectBFSPhaseZeroHigh.phase_zero_noCarry
end DirectBFSPhaseZeroHigh
