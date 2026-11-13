import Trace74CoupledPositiveT

/-! Positive trace coordinate for the exact-sign coupled Pell quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74CoupledPellTJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellHalfIndex
open Trace74CoupledExactSigns Trace74CoupledPositiveT
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Given a negative-rank magnitude `N` with the required residue and an
explicit growth bound, the very same auxiliary Pell quotient gives a
positive trace coordinate `T`. -/
theorem positive_T_from_coupled_pell (a t j s I c N : V)
    (hI : 2≤I) (hc : 0<c)
    (hnorm : I*I+delta a=delta a*(xcoord (2*t) a)*(xcoord (2*t) a))
    (hcI : c∣I) (hct : c∣t) (hcy : c=ycoord (4*j+1) a)
    (hN : N%c=(4*j+1)%c) (hfc : xcoord (2*t) a%c=(1:V)%c)
    (hlarge : xcoord (2*t) a*(N+c)≤
      oddQuotient (2*(j+t*(2*s+1))) (I-2)+c) :
    ∃ T : V, 0<T ∧
      oddQuotient (2*(j+t*(2*s+1))) (I-2)+c=
        xcoord (2*t) a*(c*T+N) := by
  let h := j+t*(2*s+1)
  let f := xcoord (2*t) a
  let Q := oddQuotient (2*h) (I-2)
  have hf : 0<f := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x (2*t) a)
  obtain ⟨hqf,hqc⟩ := exact_pair a t j s I c hI hc hnorm hcI hct hcy
  exact positive_T_of_residues Q c f N hf hc hqf (hqc.trans hN.symm) hfc hlarge

#print axioms Trace74CoupledPellTJoin.positive_T_from_coupled_pell
end Trace74CoupledPellTJoin
