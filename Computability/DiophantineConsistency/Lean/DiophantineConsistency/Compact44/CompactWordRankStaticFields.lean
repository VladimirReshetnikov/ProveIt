import DiophantineConsistency.Compact44.CompactWordRankFourFields
import DiophantineConsistency.Compact44.CompactPackingGeometry
import DiophantineConsistency.Compact44.CompactSymbolicMaskFields

/-! Chosen-rank client with the chosen dimensions and symbolic native masks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactWordRankStaticFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticPow ArithmeticPackingBlocks ArithmeticPacking
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts CompactMarkedTransport
open CompactWordLowFields CompactCanonicalPerturbation CompactRankVariation
open CompactWordRankFourFields
attribute [local irreducible] paramKernel rho lowNat highNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At the chosen dimensions, the five static bounds follow from the
geometry and exact symbolic mask theorems. The four physical block fields
remain explicit, including uniformity over every admissible selector. -/
theorem chosen_rank_static_fields (T c : V) (row : V → V) [𝚺₁-Function₁ row]
    (hw : CompactWord row (power 581197 ((2*T+3)+1)) (power 581197 (T+1)))
    (hbase : ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
      (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (baseCell row))
    (hblocks : ∀ δ : V → V, (𝚺₁-Function₁ δ) → (∀ j, δ j ≤ 1) →
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) →
      ResidualBlockFields 590069 (paramKernel rho : V) (highNat : V)
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell row) δ)) :
    ∃ δ : V → V, (𝚺₁-Function₁ δ) ∧ (∀ j, δ j ≤ 1) ∧
      (∀ j, δ j ≠ 0 → 0 < j ∧ j + 1 < power 581197 ((2*T+3)+1) ∧
        j + power 581197 (T+1) < power 581197 ((2*T+3)+1)) ∧
      PackingInput 590069 (paramKernel rho : V) CompactConcreteIncrement.mask (highNat : V)
        (power 581197 ((2*T+3)+1)) (power 581197 (T+1)) (perturb (baseCell row) δ) ∧
      windowRank (paramKernel rho : V) (power 581197 ((2*T+3)+1))
        (power 581197 (T+1)) c (perturb (baseCell row) δ) %
          (590069 * power 581197 ((2*T+3)+1)) =
        (590069 * power 581197 (T+1)) % (590069 * power 581197 ((2*T+3)+1)) := by
  have hg := CompactPackingGeometry.geometry T
  have hm := CompactSymbolicMaskFields.masks (V := V)
  rw [CompactSymbolicMaskData.low_eq] at hm
  exact chosen_rank_four_fields T (highNat : V) c row hw hg.1 hg.2 hm.1 hm.2.1 hm.2.2 hbase hblocks

#print axioms CompactWordRankStaticFields.chosen_rank_static_fields
end CompactWordRankStaticFields
