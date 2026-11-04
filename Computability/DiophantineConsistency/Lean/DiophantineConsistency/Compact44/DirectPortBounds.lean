import DiophantineConsistency.Compact44.XQ91Halt

/-! Port casts factored before specializing to huge fixed numerals. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectPortBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bounds (beta K L H : ℕ)
    (hb : 0<(beta:V)) (hl : (L:V)<(beta:V))
    (hh : (beta:V)+(H:V)<2*(beta:V)) :
    let ps := ports beta K L H
    0<(ps 0:V) ∧ (ps 2:V)<(ps 0:V) ∧ (ps 3:V)<2*(ps 0:V) := by
  refine ⟨hb,hl,?_⟩
  change ((beta+H:ℕ):V)<2*(beta:V)
  rw [Nat.cast_add]
  exact hh

#print axioms DirectPortBounds.bounds
end DirectPortBounds
