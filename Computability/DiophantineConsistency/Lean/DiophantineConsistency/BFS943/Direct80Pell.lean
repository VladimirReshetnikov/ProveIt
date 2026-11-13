import DiophantineConsistency.BFS943.Direct80Factors
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! The 80-row graph's first and doubled strong Pell facts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80Pell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellFirstNorm
open TenPositive80Graph TenPositive80Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def firstParam (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  X p v*((mu p v*Y p v)*(mu p v*Y p v))

/-- Exact graph zero gives the first Pell index and the strong Pell double.
No adjacent rational-Pell descent or halt claim is made. -/
theorem first_and_doubled (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let K := k v
    let P := firstParam p v
    let C := c p v
    let aa := D*U0*U0*E0
    ∃ tau f n I : V, 0<tau ∧ 0<f ∧ 0<n ∧ n≤K ∧
      E0=tau*tau ∧ 1+aa=f*f ∧
      xcoord n (2*(P-1)+1)=tau ∧ 2*ycoord n (2*(P-1)+1)=K ∧
      I=2*U0*tau*f ∧ 0<I ∧ (1+2*aa)*(1+2*aa)=1+D*I*I ∧
      D*(4*aa*(1+aa))=(D*I)*(D*I) ∧ C*C∣I := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let K : V := k v
  let P : V := firstParam p v
  let C : V := c p v
  let aa : V := D*U0*U0*E0
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hP : 0<P := mul_pos hx (mul_pos (mul_pos hmu hy) (mul_pos hmu hy))
  have hK : 0<K := add_pos (hv 8) (hv 9)
  have hU : 0<U0 := (factors_positive p v hb hv).2.1
  obtain ⟨tau,f,htau,hf,ht,hf2⟩ := graph_roots p v hb hv hz
  have hnorm : tau*tau=1+P*(P+1)*K*K := by
    calc
      tau*tau=E0 := ht.symm
      _=1+P*(P+1)*K*K := by dsimp [E0,E,P,firstParam,K]; ring
  obtain ⟨n,hnk,hnx,hny⟩ := positive_parameter_solution P tau K hP hnorm
  have hn : 0<n := pos_iff_ne_zero.mpr (by
    intro hn0
    apply (ne_of_gt hK)
    simpa [hn0] using hny.symm)
  change E0=tau*tau at ht
  change 1+aa=f*f at hf2
  let I : V := 2*U0*tau*f
  have hI : 0<I := mul_pos (mul_pos (mul_pos (by simp) hU) htau) hf
  have hG : E0*(1+aa)=(tau*tau)*(f*f) := by rw [ht,hf2]
  have hdbl : (1+2*aa)*(1+2*aa)=1+D*I*I := by
    calc
      (1+2*aa)*(1+2*aa)=1+4*aa*(1+aa) := by ring
      _=1+D*(2*U0)*(2*U0)*(E0*(1+aa)) := by dsimp [aa]; ring
      _=1+D*(2*U0)*(2*U0)*((tau*tau)*(f*f)) := by rw [hG]
      _=1+D*I*I := by dsimp [I]; ring
  have hQ : D*(4*aa*(1+aa))=(D*I)*(D*I) := by
    calc
      D*(4*aa*(1+aa))=(D*(2*U0))*(D*(2*U0))*(E0*(1+aa)) := by dsimp [aa]; ring
      _=(D*(2*U0))*(D*(2*U0))*((tau*tau)*(f*f)) := by rw [hG]
      _=(D*I)*(D*I) := by dsimp [I]; ring
  have hC : C*C∣I := ⟨2*v 3*tau*f,by dsimp [I,U0,U,C]; ring⟩
  exact ⟨tau,f,n,I,htau,hf,hn,hnk,ht,hf2,hnx,hny,rfl,hI,hdbl,hQ,hC⟩

#print axioms TenPositive80Pell.first_and_doubled
end TenPositive80Pell
