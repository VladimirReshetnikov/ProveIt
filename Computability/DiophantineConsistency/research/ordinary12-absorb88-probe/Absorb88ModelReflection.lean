import Absorb88FullReflection
import Absorb88Transport

/-! Bridge the negative model branch to exact full-output preservation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace Absorb88ModelReflection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88Transport
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ModelDifferenceRing Absorb88FullReflection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def reflected (v : Fin 12 → V) (first : V) : Fin 12 → V :=
  Function.update v 7 (v 7 + 2*first)

theorem model_reflection (p : Fin 4 → ℕ) (v : Fin 12 → V) (first : V)
    (negative : (pairEval (firstParts (integerPorts p)).1 v).2 =
      (pairEval (firstParts (integerPorts p)).1 v).1 + (v 0*(p 0:V))*first)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (graph (integerPorts p)).output (reflected v first) := by
  let e := (firstParts (integerPorts p)).1
  let w : Fin 12 → DiffRing V := fun i => ι (v i)
  have hneg : e.evalRing w = -((w 0 * ((integerPorts p) 0 : DiffRing V)) * ι first) := by
    have he := congrArg (fun x : V => ι x) negative
    simp only [map_add, map_mul] at he
    rw [← split_evalRing, ← evalSemiring_map, ← evalSemiring_map]
    have hc : ((integerPorts p) 0 : DiffRing V) = ι (p 0:V) := by simp [integerPorts]
    rw [hc]
    change ι (pairEval e v).1 - ι (pairEval e v).2 =
      -((ι (v 0) * ι (p 0:V))*ι first)
    rw [he]
    ring
  have hvaluation : (fun i => ι (reflected v first i)) = reflect w (ι first) := by
    funext i
    by_cases hi : i=7
    · subst i
      have htwo : (ι (2 : V) : DiffRing V) = 2 := map_ofNat ι 2
      simp [reflected,reflect,w,map_add,map_mul,htwo]
    · simp [reflected,reflect,w,hi]
  rw [internalZero_iff] at hz ⊢
  rw [hvaluation]
  rw [output_invariant (integerPorts p) w (ι first) hneg]
  exact hz

theorem negative_pair (p : Fin 4 → ℕ) (v : Fin 12 → V) (first : V)
    (hbound : (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5))
    (hnegative :
      let b : V := v 0*(p 0:V)
      let q : V := 1+b
      let k : V := v 8+v 9
      let A : V := (p 1:V)+v 5
      let Bt : V := q*((q*A)-((v 1+v 2)*A+v 1))
      b*(v 7)+b*first=(1+k*b)*Bt) :
    (pairEval (firstParts (integerPorts p)).1 v).2 =
      (pairEval (firstParts (integerPorts p)).1 v).1 + (v 0*(p 0:V))*first := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let ell : V := (X*Y)*(Y*k)
  let W : V := 1+k*b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let Bt : V := q*(Bp-Bn)
  let z := pairEval (firstParts (integerPorts p)).1 v
  have hb : Bn<Bp := hbound
  have hsplit : Bp=Bn+(Bp-Bn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hb)]
  have hprod : Bp*(W*q)=Bn*(W*q)+W*Bt := by
    calc
      Bp*(W*q)=(Bn+(Bp-Bn))*(W*q) := congrArg (fun t : V => t*(W*q)) hsplit
      _=Bn*(W*q)+W*Bt := by dsimp [Bt]; ring
  have he := root_rep p v
  change z.1+Bp*(W*q)=z.2+(b*(v 7)+Bn*(W*q)) at he
  change b*(v 7)+b*first=W*Bt at hnegative
  rw [hprod, ←hnegative] at he
  change z.2=z.1+b*first
  apply add_right_cancel (b := b*(v 7)+Bn*(W*q))
  calc
    z.2+(b*(v 7)+Bn*(W*q)) = z.1+(Bn*(W*q)+(b*(v 7)+b*first)) := he.symm
    _ = (z.1+b*first)+(b*(v 7)+Bn*(W*q)) := by ac_rfl

theorem negative_branch_preserves (p : Fin 4 → ℕ) (v : Fin 12 → V) (first : V)
    (hbound : (v 1+v 2)*((p 1:V)+v 5)+v 1 < (1+v 0*(p 0:V))*((p 1:V)+v 5))
    (hnegative :
      let b : V := v 0*(p 0:V)
      let q : V := 1+b
      let k : V := v 8+v 9
      let A : V := (p 1:V)+v 5
      let Bt : V := q*((q*A)-((v 1+v 2)*A+v 1))
      b*(v 7)+b*first=(1+k*b)*Bt)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (graph (integerPorts p)).output (reflected v first) :=
  model_reflection p v first (negative_pair p v first hbound hnegative) hz

#print axioms Absorb88ModelReflection.negative_branch_preserves
end Absorb88ModelReflection
