import DirectBFSKernelBlockSize
import DirectBFSKernelDivisibility
import DirectBFSOriginPredecessor
import CompactHighOriginResidue

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSOriginBlockResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSKernelBlockSize DirectBFSKernelDivisibility
open DirectBFSOriginPredecessor DirectBFSPackedCell DirectBFSCellSizeBound
open DirectBFSUniformPackedCell
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem four_dvd_exp {e : V} (he : 2 ≤ e) : (4 : V) ∣ Exp.exp e := by
  obtain ⟨d, rfl⟩ := exists_add_of_le he
  refine ⟨Exp.exp d, ?_⟩
  rw [add_comm, show d + 2 = d + 1 + 1 by ring, exp_succ, exp_succ]
  ring

/-- The actual low and high kernel-product halves are multiples of four;
    the high half uses the established exact split and a small input. -/
theorem low_dvd_four (x : V) : (4:V) ∣ ((paramKernel rho : V)*x % Exp.exp 590069) := by
  have hp : (4:V) ∣ (paramKernel rho : V)*x := dvd_mul_of_dvd_left kernel_model_dvd_four _
  have hmod := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<4)
    (four_dvd_exp (by norm_num : (2:V) ≤ 590069)) ((paramKernel rho : V)*x)
  apply mod_eq_zero_iff_dvd.mp
  rw [hmod, mod_eq_zero_iff_dvd.mpr hp]

theorem high_dvd_four (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    (4:V) ∣ ((paramKernel rho : V)*x / Exp.exp 590069) := by
  rw [high_product x hx]
  exact dvd_mul_of_dvd_left (four_dvd_exp (by norm_num : (2:V) ≤ 67*42)) _

/-- A marked compact word has block zero divisible by four when its
    normalized dummy cells are used. -/
theorem marked_origin_block_mod_four {row dummy : V → V} {N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (hs : 0<s) (hsN : s<N) :
    blk 590069 (paramKernel rho : V) N s
      (fun j => normalizedCell (row j) (dummy j)) 0 % 4 = 0 := by
  let X : V → V := fun j => normalizedCell (row j) (dummy j)
  have hj : cyc N 0 1 < N := cyc_lt hw.pos 0 1
  have hk : cyc N 0 s < N := cyc_lt hw.pos 0 s
  have hd (j : V) : dummy j % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt (dummy j) (by norm_num))
  have hsmall : X (cyc N 0 1) < Exp.exp (67*3297+1 : V) := by
    exact lt_of_lt_of_le (packedCell_lt_support (row (cyc N 0 1)) (dummy (cyc N 0 1)%2)
      (hw.tile_ne _ hj) (hd _)) (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hne : row (cyc N 0 s) ≠ 0 := predecessor_ne_marker hw hs hsN
  have htemp : (4:V) ∣ X (cyc N 0 s) := by
    apply mod_eq_zero_iff_dvd.mp
    exact cell_mod_four _ _ hne (hd _)
  have hlo : (4:V) ∣ lo 590069 (paramKernel rho : V) X 0 := low_dvd_four _
  have hhi : (4:V) ∣ hi 590069 (paramKernel rho : V) X (cyc N 0 1) := high_dvd_four _ hsmall
  apply mod_eq_zero_iff_dvd.mpr
  change (4:V) ∣ lo 590069 (paramKernel rho : V) X 0 +
    hi 590069 (paramKernel rho : V) X (cyc N 0 1) + X (cyc N 0 s)
  exact dvd_add (dvd_add hlo hhi) htemp

theorem normalized_high_fields {row dummy : V → V} {N s : V}
    (hw : DirectBFSLocalWord.Word row N s) (hs : 0<s) (hsN : s<N)
    (hall : ∀ j<N, NoCarry
      (blk 590069 (paramKernel rho : V) N s (fun k => normalizedCell (row k) (dummy k)) j)
      (CompactSymbolicPorts.highNat : V)) :
    NoCarry (blk 590069 (paramKernel rho : V) N s (fun k => normalizedCell (row k) (dummy k)) 0)
      ((CompactSymbolicPorts.highNat : V)-1) ∧
    ∀ j<N, 0<j → NoCarry
      (blk 590069 (paramKernel rho : V) N s (fun k => normalizedCell (row k) (dummy k)) j)
      (CompactSymbolicPorts.highNat : V) := by
  constructor
  · exact CompactHighOriginResidue.symbolic_high_origin _ (marked_origin_block_mod_four hw hs hsN) (hall 0 hw.pos)
  · intro j hj _; exact hall j hj
#print axioms DirectBFSOriginBlockResidue.low_dvd_four
#print axioms DirectBFSOriginBlockResidue.high_dvd_four
#print axioms DirectBFSOriginBlockResidue.marked_origin_block_mod_four
#print axioms DirectBFSOriginBlockResidue.normalized_high_fields
end DirectBFSOriginBlockResidue
