import P64QCube78GraphSplit
import P64QCube78Existence

/-! Draft: transport-based negative-unit exclusion for a factored 77 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube77Unit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap P64QCube78Split
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_factors {a n : DiffRing V} (h : a*n=1) (ha : a≠ -1) : a=1 ∧ n=1 := by
  have ha1 := (DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one
    ModelArithmetic.model_discrete h).resolve_right ha
  exact ⟨ha1, by simpa only [ha1,one_mul] using h⟩

theorem first_ne_neg_of_transport (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀i,0<v i)
    (hlt : InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).Lt v) :
    (P64QCube78.graph (fun j => (p j:ℤ))).A0.evalRing (fun i => ι (v i)) ≠ -1 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  let Y : V := (q*q*q)*v 7
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let k : V := v 10+v 11
  have hlt' : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff] at hlt ⊢
    change (P64QCube78.graph pp).Lt.evalRing z=0 at hlt
    rw [P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hlt
    exact hlt
  have hwp := P64QCubeMap.lift_pos p v hv
  have hgap := (P64Root.transport p w hwp hlt').1
  have hb : 0<(p 0:V) := by
    by_contra hn
    have he : (p 0:V)=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [he,zero_mul,zero_add] at hgap
    have hone : 1≤w 1+w 2 := pos_iff_one_le.mp (add_pos (hwp 1) (hwp 2))
    exact (not_lt_of_ge hone) hgap
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hq2 : 2≤q := by
    have hh := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    dsimp [q]
    have ht := add_le_add_right hh (1:V)
    simpa only [one_add_one_eq_two,add_comm] using ht
  have hX2 : 2≤X := by
    have hh := mul_le_mul (pos_iff_one_le.mp (hv 8)) hq2 (by norm_num) (by simp)
    simpa [X] using hh
  have hP2 : 2≤P := by
    have hy1 := pos_iff_one_le.mp hY
    have hh := mul_le_mul (mul_le_mul hX2 hy1 (by simp) (by simp)) hy1 (by simp) (by simp)
    simpa [P] using hh
  have hP2' : (2:DiffRing V)≤ι P := ModelArithmetic.two_le_ι hP2
  change (P64QCube78.graph pp).A0.evalRing z ≠ -1
  have hfirst : (P64QCube78.graph pp).A0.evalRing z =
      (ι (v 9):DiffRing V)*ι (v 9) - (ι P*ι k)*(ι P*ι k+ι k) := by
    rw [P64QCube78GraphSplit.first_eval]
    simp [z,pp,P,X,Y,q,k]
  rw [hfirst]
  exact norm_ne_neg _ _ _ hP2'

#print axioms P64QCube77Unit.positive_factors
#print axioms P64QCube77Unit.first_ne_neg_of_transport
end P64QCube77Unit
