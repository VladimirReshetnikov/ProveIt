import CompactHighPhaseReduction
import CompactMarkedHighPadding
import CompactMarkedCellSum

/-! Apply the phase reduction to the actual marked base and pulsed blocks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactMarkedHighReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticBinaryCarry ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactPackedCell
open CompactCanonicalPerturbation CompactMarkedTransport CompactMarkedHighPadding CompactMarkedCellSum
open CompactHighPhaseReduction
attribute [local irreducible] paramKernel rho highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Only local checks at actual nonpadding active phases remain. -/
theorem marked_high_of_active {N s : V} (row δ : V → V)
    (hw : CompactWord row N s) (hbool : ∀ j < N, δ j ≤ 1)
    (hbase : ∀ j < N, ∀ p < 8792, active p →
      NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s (fun j => packedCell (row j) 0) j) p)
        (dig 67 (highNat : V) p))
    (hpulse : ∀ j < N, ∀ p < 8792, active p →
      NoCarry (dig 67 (blk 590069 (paramKernel rho : V) N s
        (perturb (fun j => packedCell (row j) 0) δ) j) p) (dig 67 (highNat : V) p)) :
    (∀ j < N, NoCarry (blk 590069 (paramKernel rho : V) N s (fun j => packedCell (row j) 0) j) (highNat : V)) ∧
    (∀ j < N, NoCarry (blk 590069 (paramKernel rho : V) N s
      (perturb (fun j => packedCell (row j) 0) δ) j) (highNat : V)) := by
  let X0 : V → V := fun j => packedCell (row j) 0
  have hpads := marked_padding row δ hw hbool
  have hsums := marked_cell_sums row δ hw hbool
  constructor
  · intro j hj
    apply noCarry_of_active
    · exact lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le (X0 j))) (hsums.1 j hj)
    · intro p _ hp2
      exact hpads.1 j hj p hp2
    · exact hbase j hj
  · intro j hj
    apply noCarry_of_active
    · exact lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le (perturb X0 δ j))) (hsums.2 j hj)
    · intro p _ hp2
      exact hpads.2 j hj p hp2
    · exact hpulse j hj

#print axioms CompactMarkedHighReduction.marked_high_of_active
end CompactMarkedHighReduction
