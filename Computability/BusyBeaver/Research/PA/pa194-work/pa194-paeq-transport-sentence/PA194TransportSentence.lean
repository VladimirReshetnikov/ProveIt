import PA194PAeqProofTransport
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory ℒₒᵣ) [T.Δ₁] (U : Theory PA194PAeq.language) [U.Δ₁]
noncomputable def axiomSupplierSentence : ArithmeticSentence :=
  “∀ p, !((T.Δ₁ch).sigma) p → ∃ q, !formulaCodeGraph q 0 p ∧ !(provable U) q”
theorem axiomSupplier_iff : V↓[ℒₒᵣ] ⊧ axiomSupplierSentence T U ↔
    ∀ p : V, p∈T.Δ₁Class → Provable U (formulaCode 0 p) := by
  simp [axiomSupplierSentence,models_iff,Matrix.comp_vecCons'']

noncomputable def derivationTransportSentence : ArithmeticSentence :=
  “!(axiomSupplierSentence T U) → ∀ d s, !((derivationOf T).sigma) d s →
    ∃ t, !sequentGraph t s ∧ !(derivable U) t”

theorem derivationTransport_models :
    V↓[ℒₒᵣ] ⊧ derivationTransportSentence T U := by
  simp [derivationTransportSentence,models_iff,Matrix.comp_vecCons'']
  intro haxiom d s hd
  have hs : V↓[ℒₒᵣ] ⊧ axiomSupplierSentence T U := by simpa [models_iff] using haxiom
  have hd' : DerivationOf T d s := by simpa using hd
  exact derivationOf_transport T U ((axiomSupplier_iff T U).mp hs) hd'

theorem isigma1_proves_transport : 𝗜𝚺₁ ⊢ derivationTransportSentence T U := by
  apply Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro W _ _
  exact derivationTransport_models T U
#print axioms axiomSupplier_iff
#print axioms derivationTransport_models
#print axioms isigma1_proves_transport
end PA194PAeqTermBlueprint
