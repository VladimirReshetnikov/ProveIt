import P64QCube80Binding
import P64QCube80Gap
import P64QCubeExistence

/-! Positive-zero existence equivalence for the 80 and 81 quotient graphs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube80Existence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift (v : Fin 14 → V) : Fin 14 → V := Function.update v 9 (v 9 + v 7)

theorem lift_pos (v : Fin 14 → V) (hv : ∀i,0<v i) : ∀i,0<lift v i := by
  intro i
  by_cases hi : i=9
  · subst i; simpa [lift] using add_pos (hv 9) (hv 7)
  · simpa [lift,hi] using hv i

theorem lift_cast (v : Fin 14 → V) :
    (fun i => (ι (lift v i) : DiffRing V)) =
      P64QCube80Binding.liftRing (fun i => ι (v i)) := by
  funext i
  by_cases hi : i=9
  · subst i; simp [lift,P64QCube80Binding.liftRing]
  · simp [lift,P64QCube80Binding.liftRing,hi]

theorem zero_lift_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (P64QCube80.graph p).output (lift v) ↔
      InternalZero (P64QCube81.graph p).output v := by
  rw [internalZero_iff,internalZero_iff,lift_cast,P64QCube80Binding.output]

theorem quotient_of_lt (v : Fin 14 → V) (hlt : v 7 < v 9) :
    ∃rho : V, 0<rho ∧ lift (Function.update v 9 rho)=v := by
  obtain ⟨rho,hrho⟩ := exists_add_of_le (le_of_lt hlt)
  have hpos : 0<rho := by
    have h : v 7 < v 7+rho := by simpa [←hrho] using hlt
    exact (add_lt_add_iff_left (v 7)).mp (by simpa using h)
  refine ⟨rho,hpos,?_⟩
  funext i
  by_cases hi : i=9
  · subst i; simpa [lift,add_comm] using hrho.symm
  · simp [lift,hi]

theorem exists_80_of_81 (p : Fin 4 → ℕ)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v) :
    ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨lift v,lift_pos v hv,(zero_lift_iff _ v).mpr hz⟩

theorem exists_81_of_80 (p : Fin 4 → ℕ)
    (hgap : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v → v 7<v 9)
    (h : ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) :
    ∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v := by
  obtain ⟨v,hv,hz⟩ := h
  obtain ⟨rho,hrho,hlift⟩ := quotient_of_lt v (hgap v hv hz)
  let w : Fin 14 → V := Function.update v 9 rho
  have hwpos : ∀i,0<w i := by
    intro i
    by_cases hi : i=9
    · subst i; simpa [w] using hrho
    · simpa [w,hi] using hv i
  refine ⟨w,hwpos,?_⟩
  exact (zero_lift_iff _ w).mp (by simpa [w,hlift] using hz)

theorem positive_zero_iff_conditional (p : Fin 4 → ℕ)
    (hgap : ∀v : Fin 14 → V, (∀i,0<v i) →
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v → v 7<v 9) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v) :=
  ⟨exists_81_of_80 p hgap,exists_80_of_81 p⟩

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube81.graph (fun j => (p j:ℤ))).output v) :=
  positive_zero_iff_conditional p (P64QCube80Gap.graph_remainder p)

#print axioms P64QCube80Existence.positive_zero_iff
#print axioms P64QCube80Existence.lift_pos
#print axioms P64QCube80Existence.lift_cast
#print axioms P64QCube80Existence.zero_lift_iff
#print axioms P64QCube80Existence.quotient_of_lt
#print axioms P64QCube80Existence.exists_80_of_81
#print axioms P64QCube80Existence.exists_81_of_80
#print axioms P64QCube80Existence.positive_zero_iff_conditional
end P64QCube80Existence
