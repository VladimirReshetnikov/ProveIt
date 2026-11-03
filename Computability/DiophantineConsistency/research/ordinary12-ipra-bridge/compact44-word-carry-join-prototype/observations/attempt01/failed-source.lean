import CompactWordProperties
import CompactConstructedCarryInput

/-! Exact cyclic carry input for the constructed compact word. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace CompactWordCarryJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticWindowDigits
open DiophantineConsistency.CompactHeterogeneousCarry
open CompactSymbolicKernel CompactConstructedWord CompactWordProperties CompactConstructedCarryInput
open CompactPartialBandRotation CompactGenericAlignedMass CompactConcreteIndexedMass CompactTwoBandFlatten
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The represented word supplies the size and Boolean-digit hypotheses for
the exact-product carry construction. The bounded temporal term is supplied. -/
theorem word_carry (row dummy : V → V) [𝚺₁-Function₁ row] [𝚺₁-Function₁ dummy]
    (N T : V) (hN : 0 < N) (hT : T < Exp.exp (67*(8807*N))) :
    CarryInput 67 (8807*N)
      ((((paramKernel rho:ℕ):V)*(packedWord row dummy N)+T) %
        (Exp.exp (67*(8807*N))-1)) 1
      (GenericBandCarryFamily.cap (ι:=Aligned (Fin 943) (Fin 41)))
      (GenericBandCarryFamily.coefficient (fun x => (alignedCoeff selectors copies x:V)))
      (GenericBandCarryFamily.word (8807*N) (packedWord row dummy N) (bandOffsets position) T) := by
  have hn : 0 < (8807:V)*N := mul_pos (by norm_num) hN
  have hpow : (2:V) ≤ Exp.exp (67*(8807*N)) := by
    apply exp_monotone_le.mpr
    nlinarith
  have hM : 0 < Exp.exp (67*(8807*N))-1 := tsub_pos_of_lt (lt_of_lt_of_le one_lt_two hpow)
  have hC : packedWord row dummy N < Exp.exp (67*(8807*N)) := by
    simpa only [mul_assoc] using packedWord_lt row dummy N
  have hcap : ∀ k < 8807*N, dig 67 (packedWord row dummy N) k ≤ 3 := by
    intro k hk
    exact le_trans (word_cap row dummy N k hk) (by norm_num)
  exact symbolic_product_carry _ _ _ hn hM hC hcap hT

#print axioms CompactWordCarryJoin.word_carry
end CompactWordCarryJoin
