import DiophantineConsistency.Norm38ReferenceFieldsAll

/-! Conditional model-value implication; terminal agreement is a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38Reference
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem static_terminals_norms_imply_value (ports : Fin 4 → V) (w : Fin 38 → V)
    (ht : let v := NormAssignment38.assignment ports w
      let ref := reference (fun j => ι (ports j))
        (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
      pairValue ι (v 61) = ref 61 ∧ pairValue ι (v 44) = ref 44 ∧
      pairValue ι (v 78) = ref 78 ∧ pairValue ι (v 66) = ref 66 ∧
      pairValue ι (v 80) = ref 80 ∧ pairValue ι (v 36) = ref 36)
    (hn : NormAssignment38.fiveNorms ι ports w) :
    Carrier65.value (fun j => ι (ports j))
      (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1)) = 0 := by
  have hc := reference_terminal_fields_combined (fun j => ι (ports j))
    (fun j => ι (w (Fin.castLE (by decide : 14 ≤ 38) j) + 1))
  rcases ht with ⟨ht0,ht1,hta,htt,hts,htd⟩
  rcases hc with ⟨hc0,hc1,hca,hct,hcs,hcd⟩
  unfold NormAssignment38.fiveNorms at hn
  dsimp only at hn
  rw [ht0,ht1,hta,htt,hts,htd,hc0,hc1,hca,hct,hcs,hcd] at hn
  rcases hn with ⟨hP,hQ,hU,hW,hZ⟩
  simp only [Carrier65.value,hP,hQ,hU,hW,hZ,one_mul,_root_.sub_self]

end DiophantineConsistency.Norm38Reference
#print axioms DiophantineConsistency.Norm38Reference.static_terminals_norms_imply_value
