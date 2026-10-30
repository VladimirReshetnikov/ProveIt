import DiophantineConsistency.ArithmeticAdaptivePellIndices2011

/-! Exact additive q^5 congruence for the actual adaptive main root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def MainCongruence (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  ∃ s main : V, 0<s ∧ 0<main ∧ v 7=q^3*s ∧
    H*(E*q+R+1)+q^5*(s*(v 6+a*c+H*v 12)) = H*k+q^5*(s*main)

/-- Positive transport, the Y quotient, and main orientation give the additive congruence. -/
theorem main_congruence_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (htransport : TransportPositive p v)
    (hYquotient : ∃ s : V, 0<s ∧ v 7 =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V))))*s)
    (horientation : MainOriented p v) : MainCongruence p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq : 1≤q := by dsimp [q]; simp
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp htransport.2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hR : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs,hsY⟩ := hYquotient
  have hY : v 7=q^3*s := by simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hsY
  have hU : U=q^5*s := by dsimp [U]; rw [hY]; ring
  obtain ⟨main,hm,horient,_⟩ := horientation
  have hrep := main_root_rep p v hq hF
  have he := equivalent_trans (equivalent_symm hrep) horient
  change (U*(v 6+a*c)+H*(U*v 12+E*q+R'+1))+0 = H*k+U*main at he
  simp only [add_zero] at he
  rw [←hR,hU] at he
  refine ⟨s,main,hs,hm,hY,?_⟩
  calc
    H*(E*q+R+1)+q^5*(s*(v 6+a*c+H*v 12)) =
        q^5*s*(v 6+a*c)+H*(q^5*s*v 12+E*q+R+1) := by ring
    _=H*k+q^5*s*main := he
    _=H*k+q^5*(s*main) := by ring


theorem expressionAt_main_congruence (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : MainCongruence p v :=
  main_congruence_of_facts p v (expressionAt_transport_positive p v hb hv hz)
    (expressionAt_Y_quotient p v hb hv hz) (expressionAt_main_oriented p v hb hv hz)

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_main_congruence (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : MainCongruence currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_main_congruence currentPorts v hp hv
  rw [currentPorts_cast]; exact hz

theorem current_natural_main_congruence (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    MainCongruence currentPorts (fun j => v j+1) :=
  current_main_congruence _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveMainCongruence2011
