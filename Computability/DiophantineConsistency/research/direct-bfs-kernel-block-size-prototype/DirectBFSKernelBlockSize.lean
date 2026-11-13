import DirectBFSKernelLowerBound
import DirectBFSCellProduct
import DiophantineConsistency.ArithmeticPacking

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSKernelLowProduct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticMaskConstants ArithmeticWindowDigits
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSKernelLowerBound DirectBFSCellProduct
attribute [local irreducible] paramKernel rho lower
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rho_pow_cast (n : ℕ) : ((rho ^ n : ℕ) : V) = Exp.exp ((67*n : ℕ) : V) := by
  have he : rho ^ n = 2 ^ (67*n) := by unfold rho; rw [← pow_mul]
  rw [he, ← cast_exp]

theorem kernel_split_model :
    (paramKernel rho : V) = Exp.exp (67*8849 : V) + ((lower rho : ℕ) : V) := by
  have he := congrArg (fun n : ℕ => (n : V)) (DirectBFSKernelLowerBound.kernel_split rho)
  rw [Nat.cast_add,Nat.cast_mul,rho_pow_cast,rho_pow_cast] at he
  have ht : Exp.exp (67*8807 : V)*Exp.exp (67*42 : V)=Exp.exp (67*8849 : V) := by
    rw [←exp_add]
    congr 1
    norm_num
  simp only [Nat.cast_mul,Nat.cast_ofNat] at he
  rw [ht] at he
  simpa only [add_comm] using he

theorem lower_bound_model :
    ((lower rho : ℕ) : V) < Exp.exp (67*5496 : V) := by
  have h : ((lower rho : ℕ) : V) < ((rho ^ 5496 : ℕ) : V) := by
    exact_mod_cast (DirectBFSKernelLowerBound.lower_lt rho (by unfold rho; exact le_rfl))
  rw [rho_pow_cast] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- Under the already-proved cell/pulse size bound, the low component has
thirteen completely unused radix digits and 66 more unused bits before the
`2^590069` boundary. -/
theorem low_product_lt (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((lower rho : ℕ) : V) * x < Exp.exp (67*8793+1 : V) := by
  calc
    ((lower rho : ℕ) : V) * x ≤ Exp.exp (67*5496 : V) * x :=
      mul_le_mul_of_nonneg_right lower_bound_model.le (Arithmetic.zero_le x)
    _ < Exp.exp (67*5496 : V) * Exp.exp (67*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((67*5496)+(67*3297+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (67*8793+1 : V) := by
      apply congrArg Exp.exp
      norm_num

/-- The upper kernel digit is a multiple of the physical cell base, so the
product's low half is exactly the low-component product, with no remainder. -/
theorem low_product_remainder (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((paramKernel rho : V) * x) % Exp.exp 590069 =
      ((lower rho : ℕ) : V) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lower rho : ℕ) : V) * x < Exp.exp 590069 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (67*8793+1 : V) ≤ 590069))
  have htop : Exp.exp (67*8849 : V) = Exp.exp 590069 * Exp.exp (67*42 : V) := by
    rw [← exp_add]
    congr 1
    norm_num
  rw [kernel_split_model, htop]
  have hm : (Exp.exp 590069 * Exp.exp (67*42) + ((lower rho : ℕ) : V)) * x =
      ((lower rho : ℕ) : V) * x + Exp.exp 590069 * (Exp.exp (67*42) * x) := by ring
  rw [hm, mod_add_mul' _ _ (exp_pos (590069:V)), mod_eq_self_of_lt hbase]

#print axioms DirectBFSKernelLowProduct.rho_pow_cast
#print axioms DirectBFSKernelLowProduct.kernel_split_model
#print axioms DirectBFSKernelLowProduct.lower_bound_model
#print axioms DirectBFSKernelLowProduct.low_product_lt
#print axioms DirectBFSKernelLowProduct.low_product_remainder
end DirectBFSKernelLowProduct

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSKernelBlockSize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSKernelLowerBound DirectBFSKernelLowProduct
attribute [local irreducible] paramKernel rho lower
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The high half comes exclusively from the isolated top kernel digit. -/
theorem high_product (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((paramKernel rho : V) * x) / Exp.exp 590069 = Exp.exp (67*42) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lower rho : ℕ) : V) * x < Exp.exp 590069 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (67*8793+1 : V) ≤ 590069))
  have htop : Exp.exp (67*8849 : V) = Exp.exp 590069 * Exp.exp (67*42 : V) := by
    rw [← exp_add]
    congr 1
    norm_num
  rw [kernel_split_model, htop]
  have hm : (Exp.exp 590069 * Exp.exp (67*42) + ((lower rho : ℕ) : V)) * x =
      (Exp.exp (67*42) * x) * Exp.exp 590069 + ((lower rho : ℕ) : V) * x := by ring
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
    have he : Exp.exp ((67*8793+1)+1+1 : V) =
        2*(2*Exp.exp (67*8793+1 : V)) := by rw [exp_succ, exp_succ]
    calc
      E+E+E+E = 2*(2*Exp.exp (67*8793+1 : V)) := by unfold E; ring
      _ = Exp.exp ((67*8793+1)+1+1 : V) := he.symm
      _ = Exp.exp (67*8793+3 : V) := by apply congrArg Exp.exp; ring
  rw [hfour] at hsum
  exact lt_of_lt_of_le (by simpa [blk] using hsum)
    (exp_monotone_le.mpr (by norm_num : (67*8793+3 : V) ≤ 590069))

#print axioms DirectBFSKernelBlockSize.high_product
#print axioms DirectBFSKernelBlockSize.high_product_lt
#print axioms DirectBFSKernelBlockSize.cell_sum_of_small
end DirectBFSKernelBlockSize
