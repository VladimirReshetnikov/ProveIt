import DiophantineConsistency.Compact44.P64Root

/-! Draft: quotient-coordinate maps for package 64's Y carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCubeMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift (p : Fin 4 → ℕ) (v : Fin 14 → V) : Fin 14 → V :=
  let q : V := (p 0:V)*v 0+1
  Function.update v 7 ((q*q*q)*v 7)

theorem lift_pos (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i) :
    ∀i,0<lift p v i := by
  intro i
  by_cases hi : i=7
  · subst i
    have hq : 0<(p 0:V)*v 0+1 := by simp
    simpa [lift] using mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  · simpa [lift,hi] using hv i

theorem quotient_of_first_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hz : InternalZero (P64Graph.graph (fun j => (p j:ℤ))).A0 v) :
    ∃s : V, 0<s ∧ lift p (Function.update v 7 s)=v := by
  let q : V := (p 0:V)*v 0+1
  have hq : 0<q := by dsimp [q]; simp
  have hq3 : 0<q*q*q := mul_pos (mul_pos hq hq) hq
  have hd := (P64Root.first_root p v hz).1
  change q*q*q ∣ v 7 at hd
  obtain ⟨s,hs⟩ := hd
  have hspos : 0<s := pos_of_mul_pos_right (by rw [←hs]; exact hv 7) (by simp)
  refine ⟨s,hspos,?_⟩
  funext i
  by_cases hi : i=7
  · subst i
    simpa [lift,q] using hs.symm
  · simp [lift,hi]

section Ring
variable {R : Type*} [CommRing R]

def liftRing (p : Fin 4 → ℤ) (v : Fin 14 → R) : Fin 14 → R :=
  let q := (p 0:R)*v 0+1
  Function.update v 7 ((q*q*q)*v 7)

theorem first_factor (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Q := q*q*q
    let Y := Q*v 7
    let k := v 10+v 11
    let ell := (v 8*q)*Y*(k*Y)
    (P64Graph.graph p).A0.evalRing (liftRing p v) =
      Q*Q*((ell+v 9+v 7)*(ell+v 9+v 7)-(ell*(ell+k)+1)) := by
  rw [P64Graph.A0_eval]
  simp [P64Graph.vals,liftRing]
  ring

end Ring

theorem lift_cast (p : Fin 4 → ℕ) (v : Fin 14 → V) :
    (fun i => (ι (lift p v i) : DiffRing V)) =
      liftRing (fun j => (p j:ℤ)) (fun i => ι (v i)) := by
  funext i
  by_cases hi : i=7
  · subst i
    simp only [lift,liftRing,Function.update_self,map_mul,map_add,map_one,P64Root.cast_nat]
  · simp [lift,liftRing,hi]

#print axioms P64QCubeMap.lift_pos
#print axioms P64QCubeMap.quotient_of_first_zero
#print axioms P64QCubeMap.first_factor
#print axioms P64QCubeMap.lift_cast
end P64QCubeMap
