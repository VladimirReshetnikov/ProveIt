import CompactKernelLowProduct
import DiophantineConsistency.ArithmeticPacking

/-! The exact low and high kernel halves give uniform transport-block size
bounds, assuming the supplied represented cells are sufficiently small. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactKernelBlockSize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactKernelSplit CompactKernelLowProduct
attribute [local irreducible] paramKernel rho lowerKernelAt
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The high half comes exclusively from the isolated top kernel digit. -/
theorem high_product (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((paramKernel rho : V) * x) / Exp.exp 590069 = Exp.exp (67*42) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp 590069 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (67*8793+1 : V) ≤ 590069))
  have htop : Exp.exp (67*8849 : V) = Exp.exp 590069 * Exp.exp (67*42 : V) := by
    rw [← exp_add]
    congr 1
    norm_num
  rw [kernel_split_model, htop]
  have hm : (Exp.exp 590069 * Exp.exp (67*42) + ((lowerKernelAt rho : ℕ) : V)) * x =
      (Exp.exp (67*42) * x) * Exp.exp 590069 + ((lowerKernelAt rho : ℕ) : V) * x := by ring
  rw [hm, div_mul_add _ _ hbase]

theorem high_product_lt (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((paramKernel rho : V) * x) / Exp.exp 590069 < Exp.exp (67*3339+1 : V) := by
  rw [high_product x hx]
  calc
    Exp.exp (67*42 : V) * x < Exp.exp (67*42 : V) * Exp.exp (67*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((67*42)+(67*3297+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (67*3339+1 : V) := by apply congrArg Exp.exp; norm_num

/-- Pointwise size alone suffices for the full cell-plus-transport-block
bound; all three cyclic indices are in range when N is positive. -/
theorem cell_sum_of_small {N s : V} {X : V → V}
    (hN : 0 < N) (hsmall : ∀ j < N, X j < Exp.exp (67*3297+1 : V)) :
    ∀ j < N, X j + blk 590069 (paramKernel rho : V) N s X j < Exp.exp 590069 := by
  intro j hj
  have h0 := hsmall j hj
  have h1 := hsmall (cyc N j 1) (cyc_lt hN j 1)
  have hs := hsmall (cyc N j s) (cyc_lt hN j s)
  let E : V := Exp.exp (67*8793+1)
  have hx : X j < E := lt_of_lt_of_le h0 (exp_monotone_le.mpr (by norm_num))
  have hs' : X (cyc N j s) < E := lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hl : lo 590069 (paramKernel rho : V) X j < E := by
    unfold lo E
    rw [low_product_remainder (X j) h0]
    exact low_product_lt (X j) h0
  have hh : hi 590069 (paramKernel rho : V) X (cyc N j 1) < E := by
    unfold hi E
    exact lt_of_lt_of_le (high_product_lt _ h1) (exp_monotone_le.mpr (by norm_num))
  have hsum : X j + (lo 590069 (paramKernel rho : V) X j +
      hi 590069 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) < E+E+E+E := by
    have ha := add_lt_add hx hl
    have hb := add_lt_add hh hs'
    calc
      _ = (X j + lo 590069 (paramKernel rho : V) X j) +
          (hi 590069 (paramKernel rho : V) X (cyc N j 1) + X (cyc N j s)) := by ring
      _ < (E+E)+(E+E) := add_lt_add ha hb
      _ = E+E+E+E := by ring
  have hfour : E+E+E+E = Exp.exp (67*8793+3 : V) := by
    unfold E
    rw [show (67*8793+3:V)=(67*8793+1)+1+1 by ring, exp_succ, exp_succ]
    ring
  rw [hfour] at hsum
  exact lt_of_lt_of_le (by simpa [blk] using hsum)
    (exp_monotone_le.mpr (by norm_num : (67*8793+3 : V) ≤ 590069))

#print axioms CompactKernelBlockSize.high_product
#print axioms CompactKernelBlockSize.high_product_lt
#print axioms CompactKernelBlockSize.cell_sum_of_small
end CompactKernelBlockSize
