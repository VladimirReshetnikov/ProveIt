import P64QCube79Binding
import P64QCube80Gap
import P64QCube80Existence

/-! Draft: positive-zero existence equivalence for the 79 and 80 graphs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube79Gap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ell (p : Fin 4 → ℕ) (v : Fin 14 → V) : V :=
  let q := (p 0:V)*v 0+1
  let Y := q*q*q*v 7
  (v 8*q)*Y*((v 10+v 11)*Y)

def lift79 (p : Fin 4 → ℕ) (v : Fin 14 → V) : Fin 14 → V :=
  Function.update v 9 (ell p v + v 9)

theorem lift_pos (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i) :
    ∀i,0<lift79 p v i := by
  intro i
  by_cases hi : i=9
  · subst i; simp [lift79, hv]
  · simpa [lift79,hi] using hv i

theorem lift_cast (p : Fin 4 → ℕ) (v : Fin 14 → V) :
    (fun i => (ι (lift79 p v i) : DiffRing V)) =
      P64QCube79Binding.liftRing (fun j => (p j:ℤ)) (fun i => ι (v i)) := by
  funext i
  by_cases hi : i=9
  · subst i; simp [lift79,ell,P64QCube79Binding.liftRing,P64QCube79Binding.ell]
  · simp [lift79,P64QCube79Binding.liftRing,hi]

theorem zero_lift_iff (p : Fin 4 → ℕ) (v : Fin 14 → V) :
    InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output (lift79 p v) ↔
      InternalZero (P64QCube80.graph (fun j => (p j:ℤ))).output v := by
  rw [internalZero_iff,internalZero_iff,lift_cast,P64QCube79Binding.output]

theorem main_same (p : Fin 4 → ℤ) : (P64QCube79.graph p).M=(P64QCube81.graph p).M := by rfl
theorem strong_same (p : Fin 4 → ℤ) : (P64QCube79.graph p).W=(P64QCube81.graph p).W := by rfl
theorem auxiliary_same (p : Fin 4 → ℤ) : (P64QCube79.graph p).Na=(P64QCube81.graph p).Na := by rfl
theorem transport_same (p : Fin 4 → ℤ) : (P64QCube79.graph p).Lt=(P64QCube81.graph p).Lt := by rfl
theorem output_shape (p : Fin 4 → ℤ) : (P64QCube79.graph p).output =
    (P64QCube79.graph p).A0*(P64QCube79.graph p).A0+
    (P64QCube79.graph p).M*(P64QCube79.graph p).M+
    (P64QCube79.graph p).W*(P64QCube79.graph p).W+
    (P64QCube79.graph p).Na*(P64QCube79.graph p).Na+
    (P64QCube79.graph p).Lt*(P64QCube79.graph p).Lt-1 := by rfl

theorem first_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P64QCube79.graph p).A0.evalRing v =
      v 9*v 9-(P64QCube79Binding.ell p v*(P64QCube79Binding.ell p v+(v 10+v 11))+1) := by
  simp [P64QCube79.graph,P64QCube79Binding.ell,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem graph_root_gt (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube79.graph (fun j => (p j:ℤ))).output v) :
    ell p v < v 9 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let first : DiffRing V := (P64QCube79.graph pp).A0.evalRing z
  have hs : first*first+(P64QCube79.graph pp).M.evalRing z*(P64QCube79.graph pp).M.evalRing z+
      (P64QCube79.graph pp).W.evalRing z*(P64QCube79.graph pp).W.evalRing z+
      (P64QCube79.graph pp).Na.evalRing z*(P64QCube79.graph pp).Na.evalRing z+
      (P64QCube79.graph pp).Lt.evalRing z*(P64QCube79.graph pp).Lt.evalRing z=1 := by
    have hh := hz
    rw [internalZero_iff,output_shape] at hh
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  rw [main_same pp,strong_same pp,auxiliary_same pp,transport_same pp,
    ←P64QCubeBinding.main pp z,←P64QCubeBinding.strong pp z,
    ←P64QCubeBinding.auxiliary pp z,←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hs
  obtain ⟨hfirst,_,_,_,_⟩ := P64NormFirstReplacement.residuals p w (P64QCubeMap.lift_pos p v hv) first hs
  have hn : (ι (v 9) : DiffRing V)*(ι (v 9)) =
      ι (ell p v)*(ι (ell p v)+ι (v 10+v 11))+1 := by
    change (P64QCube79.graph pp).A0.evalRing z=0 at hfirst
    rw [first_eval] at hfirst
    simp only [z,pp,ell,P64QCube79Binding.ell,P64Root.cast_nat,map_add,map_mul,map_one] at hfirst ⊢
    linear_combination hfirst
  have he : (0:DiffRing V) ≤ ι (ell p v) := ι_nonneg _
  have hk : (0:DiffRing V) ≤ ι (v 10+v 11) := ι_nonneg _
  have hr : (0:DiffRing V) ≤ ι (v 9) := ι_nonneg _
  apply ι_lt_ι.mp
  by_contra h
  have hle : (ι (v 9):DiffRing V) ≤ ι (ell p v) := le_of_not_gt h
  have hsq := mul_le_mul hle hle hr he
  have hp := mul_nonneg he hk
  nlinarith only [hn,hsq,hp]

#print axioms P64QCube79Gap.graph_root_gt
end P64QCube79Gap
