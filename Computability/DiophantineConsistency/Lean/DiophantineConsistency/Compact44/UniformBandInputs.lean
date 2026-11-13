import DiophantineConsistency.Compact44.UniformForeignZero
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace UniformBandInputs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactSymbolicKernel CompactPartialBand
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_phase (N k : V) (T j : ℕ) (hN : 0<N) (hT : T<8807) (hj : j≤T)
    (hp : k%8807=(T:V)) :
    (cyc (8807*N) k (((T-j):ℕ):V))%8807=(j:V) := by
  rw [CyclicAnyPhase.cyc_period 8807 N k (((T-j):ℕ):V) (by norm_num) hN,hp]
  exact SelectedBandInputs.source_index (8807:V) T j (by exact_mod_cast hT) hj

def Inputs (n C k : V) (T : ℕ) : Prop :=
    (∀ j : Fin 943, selectorDigit n C k T j≤1) ∧
    (∀ j : Fin 41, copyDigit position n C k T j≤1) ∧
    (∑ j : Fin 41, (2:V)^j.val*copyDigit position n C k T j)<Exp.exp 41

theorem inputs (N C k : V) (T : ℕ) (hN : 0<N) (hT : 3296≤T) (hTmax : T<8807)
    (hp : k%8807=(T:V))
    (hbool : ∀ j<8807*N, j%8807≠1063 → dig 67 C j≤1) : Inputs (8807*N) C k T := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  have hsel : ∀ j : Fin 943, selectorDigit (8807*N) C k T j≤1 := by
    intro j
    have hjT : j.val≤T := le_trans (by have := j.isLt; omega) hT
    have hjsp : (j.val:V)≠1063 := by
      intro he
      have he' : j.val=1063 := by exact_mod_cast he
      have := j.isLt
      omega
    unfold selectorDigit
    apply hbool _ (cyc_lt hn _ _)
    rw [source_phase N k T j.val hN hTmax hjT hp]
    exact hjsp
  have hcopy : ∀ j : Fin 41, copyDigit position (8807*N) C k T j≤1 := by
    intro j
    have hall := ForeignBandGeometry.copy_allowed j
    unfold ForeignBandGeometry.Allowed at hall
    have hjT : position j≤T := le_trans (by omega) hT
    have hjsp : (position j:V)≠1063 := by
      intro he
      have he' : position j=1063 := by exact_mod_cast he
      omega
    unfold copyDigit
    apply hbool _ (cyc_lt hn _ _)
    rw [source_phase N k T (position j) hN hTmax hjT hp]
    exact hjsp
  exact ⟨hsel,hcopy,CompactCopyBound.copy_bound _ hcopy⟩
#print axioms UniformBandInputs.source_phase
#print axioms UniformBandInputs.inputs
end UniformBandInputs
