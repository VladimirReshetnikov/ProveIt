import DiophantineConsistency.Compact44.BandCarryInputs
import DiophantineConsistency.Compact44.CompactHeterogeneousCarry
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace GenericBandCarryFamily
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticCyclicWord ArithmeticWindowDigits CompactHeterogeneousCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {ι : Type*} [Fintype ι]

def coefficient (a : ι → V) : ι ⊕ Unit → V
  | .inl i => a i
  | .inr _ => 1

def word (n C : V) (e : ι → V) (T : V) : ι ⊕ Unit → V
  | .inl i => rot 67 n C (e i%n)
  | .inr _ => T

def cap : ι ⊕ Unit → V
  | .inl _ => 3
  | .inr _ => Exp.exp 67-1

theorem carry_input (n C T F b : V) (a e : ι → V)
    (hn : 0<n) (hM : 0<Exp.exp (67*n)-1)
    (hC : C<Exp.exp (67*n)) (hCcap : ∀ k<n, dig 67 C k≤3)
    (hT : T<Exp.exp (67*n)) (hTcap : ∀ k<n, dig 67 T k≤Exp.exp 67-1)
    (hF : F<Exp.exp (67*n)-1)
    (hgraph : ((∑ i, a i*rot 67 n C (e i%n)) + T) % (Exp.exp (67*n)-1)=F)
    (hmass : ((∑ i, a i*3)+(Exp.exp 67-1))+1 ≤ (b+1)*(Exp.exp 67-1)) :
    CarryInput 67 n F b (cap (ι:=ι)) (coefficient a) (word n C e T) := by
  refine ⟨hn,hM,?_,?_,hF,?_,?_⟩
  · intro i
    cases i with
    | inl i => exact (BandCarryInputs.aligned_rotation_bounds n C (e i) 3 hn hC hCcap).1
    | inr i => exact hT
  · intro i k hk
    cases i with
    | inl i => exact (BandCarryInputs.aligned_rotation_bounds n C (e i) 3 hn hC hCcap).2 k hk
    | inr i => exact hTcap k hk
  · simp only [Fintype.sum_sum_type, Fintype.sum_unique, coefficient, word, one_mul]
    rw [hgraph, mod_eq_self_of_lt hF]
  · simpa only [Fintype.sum_sum_type, Fintype.sum_unique, coefficient, cap, one_mul] using hmass
#print axioms GenericBandCarryFamily.carry_input
end GenericBandCarryFamily
