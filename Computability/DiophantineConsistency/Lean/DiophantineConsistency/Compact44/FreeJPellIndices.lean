import DiophantineConsistency.Compact44.FreeJMainOrientation
import DiophantineConsistency.ArithmeticAdaptivePellIndices2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJPellIndices
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticPellClassification
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellFirstNorm
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding FreeJMainOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def FreeJIndices (p : Fin 4 → ℕ) (v : Fin 12 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let M : V := (q*(q*q))*(v 0*(p 0:V))
  let U : V := v 6*(q*q)
  let Q : V := (v 5*v 6)*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := v 5*v 6+v 6
  ∃ first main n m : V, 0<first ∧ 0<main ∧ 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧
    magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first ∧
    Equivalent (pairEval (core (fun j => (p j:ℤ))).d v) (natural (U*main)) ∧
    xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
    xcoord m a=main ∧ ycoord m a=c

theorem indices (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) : FreeJIndices p v := by
  let Q : V := (v 5*v 6)*v 6
  let k : V := v 8+v 9
  let c : V := v 8+v 6*k
  let a : V := v 5*v 6+v 6
  have hQ : 0<Q := mul_pos (mul_pos (hv 5) (hv 6)) (hv 6)
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have hc : 0<c := add_pos (hv 8) (mul_pos (hv 6) hk)
  have hq : 0<1+v 0*(p 0:V) := by simp
  have hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)) :=
    mul_pos (mul_pos hq (mul_pos hq hq)) (mul_pos (hv 0) hb)
  obtain ⟨first,hroot,hnorm⟩ := scaled_quotient _ _ _ hM (first_scaled_norm p v hz)
  have hf : 0<first := pos_of_mul_pos_left (by rw [hnorm]; simp) (by simp)
  obtain ⟨main,hm,hmain,hmnorm⟩ := main_oriented p v hb hv hz
  have hn : first*first=1+Q*(Q+1)*k*k := by
    calc
      first*first=1+((v 5*v 6)*(v 6*k))*(((v 5*v 6)*(v 6*k))+k) := hnorm
      _=1+Q*(Q+1)*k*k := by dsimp [Q]; ring
  have hmn : main*main=1+delta a*c*c := by
    calc
      main*main=1+((3+4*a)+a*a)*(c*c) := hmnorm
      _=1+delta a*c*c := by unfold delta; ring
  obtain ⟨n,hnk,hnx,hny⟩ := ArithmeticPellFirstNorm.positive_parameter_solution Q first k hQ hn
  obtain ⟨m,hmc,hmx,hmy⟩ := ArithmeticPellClassification.solution_index a main c hmn
  have hnp : 0<n := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hk) (by simpa [h] using hny.symm))
  have hmp : 0<m := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hc) (by simpa [h] using hmy.symm))
  exact ⟨first,main,n,m,hf,hm,hnp,hmp,hnk,hmc,hroot,hmain,hnx,hny,hmx,hmy⟩


end FreeJPellIndices
#print axioms FreeJPellIndices.indices
