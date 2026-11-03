import DirectBFSKernelBlockSize
import DirectBFSCellSharpSize
import DirectBFSKernelLowerMassAlias

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSHighPaddingSize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticMaskConstants ArithmeticCyclicWord ArithmeticPacking
open CompactSymbolicKernel DirectBFSSymbolicKernel DirectBFSKernelLowerBound DirectBFSKernelLowProduct
open DirectBFSKernelBlockSize DirectBFSCellSharpSize DirectBFSKernelLowerMassAlias DirectBFSPackedCell
attribute [local irreducible] paramKernel rho DirectBFSKernelLowerBound.lower
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem lower_mass_model :
    ((DirectBFSKernelLowerBound.lower rho : ℕ) : V) ≤ Exp.exp (67*5495+62 : V) := by
  have hr : 1 ≤ rho := by unfold rho; norm_num
  have hn := DirectBFSKernelLowerMassAlias.lower_le rho hr
  have hv : ((DirectBFSKernelLowerBound.lower rho : ℕ) : V) ≤ ((2^62 * rho^5495 : ℕ) : V) := by
    exact_mod_cast hn
  calc
    _ ≤ ((2^62 * rho^5495 : ℕ) : V) := hv
    _ = Exp.exp (62:V) * Exp.exp (67*5495 : V) := by
      rw [Nat.cast_mul, ← cast_exp 62, rho_pow_cast]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ = Exp.exp (67*5495+62 : V) := by
      rw [← exp_add]
      apply congrArg Exp.exp
      ring

theorem sharp_cell (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < Exp.exp (67*3296+1 : V) := by
  rw [exp_succ]
  exact packedCell_lt_twice_top a d ha hd

theorem low_product_sharp (x : V) (hx : x < Exp.exp (67*3296+1 : V)) :
    ((DirectBFSKernelLowerBound.lower rho : ℕ) : V) * x < Exp.exp (67*8791+63 : V) := by
  calc
    ((DirectBFSKernelLowerBound.lower rho : ℕ) : V) * x ≤ Exp.exp (67*5495+62 : V) * x :=
      mul_le_mul_of_nonneg_right lower_mass_model (Arithmetic.zero_le x)
    _ < Exp.exp (67*5495+62 : V) * Exp.exp (67*3296+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((67*5495+62)+(67*3296+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (67*8791+63 : V) := by apply congrArg Exp.exp; norm_num

theorem block_lt_padding {N s : V} {X : V → V} (hN : 0 < N)
    (hsmall : ∀ j < N, X j < Exp.exp (67*3296+1 : V)) :
    ∀ j < N, blk 590069 (paramKernel rho : V) N s X j < Exp.exp (67*8792 : V) := by
  intro j hj
  have h0 := hsmall j hj
  have h1 := hsmall (cyc N j 1) (cyc_lt hN j 1)
  have hs := hsmall (cyc N j s) (cyc_lt hN j s)
  have h0' : X j < Exp.exp (67*3297+1 : V) :=
    lt_of_lt_of_le h0 (exp_monotone_le.mpr (by norm_num))
  have h1' : X (cyc N j 1) < Exp.exp (67*3297+1 : V) :=
    lt_of_lt_of_le h1 (exp_monotone_le.mpr (by norm_num))
  let E : V := Exp.exp (67*8791+63)
  have hl : lo 590069 (paramKernel rho : V) X j < E := by
    unfold lo E
    rw [low_product_remainder (X j) h0']
    exact low_product_sharp (X j) h0
  have hh : hi 590069 (paramKernel rho : V) X (cyc N j 1) < E := by
    unfold hi E
    exact lt_of_lt_of_le (high_product_lt _ h1') (exp_monotone_le.mpr (by norm_num))
  have ht : X (cyc N j s) < E :=
    lt_of_lt_of_le hs (exp_monotone_le.mpr (by norm_num))
  have hsum : blk 590069 (paramKernel rho : V) N s X j < E+E+E := by
    unfold blk
    exact add_lt_add (add_lt_add hl hh) ht
  have hless : E+E+E ≤ E+E+E+E := le_add_of_nonneg_right (Arithmetic.zero_le E)
  have hfour : E+E+E+E = Exp.exp (67*8791+65 : V) := by
    have he : Exp.exp ((67*8791+63)+1+1 : V) =
        2*(2*Exp.exp (67*8791+63 : V)) := by rw [exp_succ, exp_succ]
    calc
      E+E+E+E = 2*(2*Exp.exp (67*8791+63 : V)) := by unfold E; ring
      _ = Exp.exp ((67*8791+63)+1+1 : V) := he.symm
      _ = Exp.exp (67*8791+65 : V) := by apply congrArg Exp.exp; ring
  exact lt_of_lt_of_le hsum (le_trans hless (by
    rw [hfour]
    exact exp_monotone_le.mpr (by norm_num)))

#print axioms DirectBFSHighPaddingSize.lower_mass_model
#print axioms DirectBFSHighPaddingSize.sharp_cell
#print axioms DirectBFSHighPaddingSize.low_product_sharp
#print axioms DirectBFSHighPaddingSize.block_lt_padding
end DirectBFSHighPaddingSize
