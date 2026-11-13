import P64QCube79Gap
import P64QCube80Existence

/-! Positive-zero existence equivalence for the 79 and 80 graphs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube79Existence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open P64QCube79Gap

theorem quotient_of_lt (p : Fin 4 → ℕ) (v : Fin 14 → V) (hlt : ell p v < v 9) :
    ∃rho : V, 0<rho ∧ lift79 p (Function.update v 9 rho)=v := by
  obtain ⟨rho,hrho⟩ := exists_add_of_le (le_of_lt hlt)
  have hpos : 0<rho := by
    have h : ell p v < ell p v+rho := by simpa [←hrho] using hlt
    exact (add_lt_add_iff_left (ell p v)).mp (by simpa using h)
  refine ⟨rho,hpos,?_⟩
  funext i
  by_cases hi : i=9
  · subst i; simpa [lift79,ell,add_comm] using hrho.symm
  · simp [lift79,hi]

theorem exists_79_of_80 (p : Fin 4 → ℕ)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) :
    ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨lift79 p v,lift_pos p v hv,(zero_lift_iff p v).mpr hz⟩

theorem exists_80_of_79 (p : Fin 4 → ℕ)
    (hgap : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v → ell p v<v 9)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) :
    ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v := by
  obtain ⟨v,hv,hz⟩ := h
  obtain ⟨rho,hrho,hlift⟩ := quotient_of_lt p v (hgap v hv hz)
  let w : Fin 14 → V := Function.update v 9 rho
  have hwpos : ∀i,0<w i := by
    intro i
    by_cases hi : i=9
    · subst i; simpa [w] using hrho
    · simpa [w,hi] using hv i
  refine ⟨w,hwpos,?_⟩
  exact (zero_lift_iff p w).mp (by simpa [w,hlift] using hz)

theorem positive_zero_iff_conditional (p : Fin 4 → ℕ)
    (hgap : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v → ell p v<v 9) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) :=
  ⟨exists_80_of_79 p hgap,exists_79_of_80 p⟩

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) :=
  positive_zero_iff_conditional p (graph_root_gt p)

#print axioms P64QCube79Existence.positive_zero_iff
#print axioms P64QCube79Existence.quotient_of_lt
#print axioms P64QCube79Existence.exists_79_of_80
#print axioms P64QCube79Existence.exists_80_of_79
#print axioms P64QCube79Existence.positive_zero_iff_conditional
end P64QCube79Existence
