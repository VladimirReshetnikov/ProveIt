import P64QCube78Binding
import P64QCube78GraphSplit
import P64QCube79Gap

/-! Draft: positive-zero equivalence for the shifted 78 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube78Existence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_first_eq_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) :
    (P64QCube79.graph (fun j => (p j:ℤ))).A0.evalRing (fun i => ι (v i)) = 0 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let first : DiffRing V := (P64QCube79.graph pp).A0.evalRing z
  have hs : first*first+(P64QCube79.graph pp).M.evalRing z*(P64QCube79.graph pp).M.evalRing z+
      (P64QCube79.graph pp).W.evalRing z*(P64QCube79.graph pp).W.evalRing z+
      (P64QCube79.graph pp).Na.evalRing z*(P64QCube79.graph pp).Na.evalRing z+
      (P64QCube79.graph pp).Lt.evalRing z*(P64QCube79.graph pp).Lt.evalRing z=1 := by
    have hh := hz
    rw [internalZero_iff,P64QCube79Gap.output_shape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  rw [P64QCube79Gap.main_same pp,P64QCube79Gap.strong_same pp,
    P64QCube79Gap.auxiliary_same pp,P64QCube79Gap.transport_same pp,
    ←P64QCubeBinding.main pp z,←P64QCubeBinding.strong pp z,
    ←P64QCubeBinding.auxiliary pp z,←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hs
  obtain ⟨hf,_,_,_,_⟩ := P64NormFirstReplacement.residuals p w (P64QCubeMap.lift_pos p v hv) first hs
  exact hf

theorem same_zero_iff (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i) :
    InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v ↔
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun j => ι (v j)
  constructor
  · intro hz
    have ha := P64QCube78GraphSplit.first_eq_one p v hv hz
    change (P64QCube78.graph pp).A0.evalRing z = 1 at ha
    rw [P64QCube78Binding.first] at ha
    have hzero : (P64QCube79.graph pp).A0.evalRing z=0 := by linarith
    rw [internalZero_iff] at hz ⊢
    change (P64QCube78.graph pp).output.evalRing z=0 at hz
    change (P64QCube79.graph pp).output.evalRing z=0
    rw [P64QCube78Binding.output,hzero] at hz
    simpa using hz
  · intro hz
    have ha := old_first_eq_zero p v hv hz
    change (P64QCube79.graph pp).A0.evalRing z=0 at ha
    rw [internalZero_iff] at hz ⊢
    change (P64QCube79.graph pp).output.evalRing z=0 at hz
    change (P64QCube78.graph pp).output.evalRing z=0
    rw [P64QCube78Binding.output,ha]
    simpa using hz

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · exact ⟨v,hv,(same_zero_iff p v hv).mp hz⟩
  · exact ⟨v,hv,(same_zero_iff p v hv).mpr hz⟩

#print axioms P64QCube78Existence.old_first_eq_zero
#print axioms P64QCube78Existence.same_zero_iff
#print axioms P64QCube78Existence.positive_zero_iff
end P64QCube78Existence
