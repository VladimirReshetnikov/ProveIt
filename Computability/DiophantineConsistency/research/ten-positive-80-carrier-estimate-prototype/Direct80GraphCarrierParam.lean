import Direct80CarrierEstimate
import CarrierSizes
import Direct80CAboveX
import Direct80ResidueBinding

/-! Bind the first signed-carrier estimate to every positive 80 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80GraphCarrierParam
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80Adjacent TenPositive80ResidueBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bound_for_witnesses (p : Fin 4 → ℕ) (v : Fin 10 → V) (tau f V0 y : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v)
    (ht : 0<tau) (hf : 0<f) (hV : 0<V0)
    (hE : E p v=tau*tau)
    (hf2 : 1+delta p v*U p v*U p v*E p v=f*f)
    (hVs : (graph (integerPorts p)).v.evalRing (fun j => ι (v j)) *
      (graph (integerPorts p)).v.evalRing (fun j => ι (v j)) = ι (V0*V0))
    (haux : let a := delta p v*U p v*U p v*E p v
      let Q := delta p v*(4*a*(1+a))
      Q*(V0*V0)=1+(Q-1)*(y*y)) :
    2*(tau*f*y)<V0*V0 := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let C : V := c p v
  let AA : V := A p v
  let a : V := D*U0*U0*E0
  let F : V := 1+2*a
  let Q : V := D*(4*a*(1+a))
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hq1 : 1≤q p v := pos_iff_one_le.mp hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hX1 : 1≤X p v := pos_iff_one_le.mp hX
  have hcgt : 1<C := lt_of_le_of_lt hX1 (Direct80CAboveX.graph_c_above_x p v hb hv hz)
  have hc1 : 1≤C := le_of_lt hcgt
  have hmu2 : (2:V)≤mu p v := by
    dsimp [mu]
    have hh := add_le_add_right (one_le_mul hq1 hq1) 1
    simpa only [add_comm,show (1:V)+1=2 by ring] using hh
  have hS2 : (2:V)≤mu p v*Y p v := le_trans hmu2 (le_mul_of_one_le_right (by simp) hY1)
  have hXplus : (2:V)≤X p v+1 := by
    have hh := add_le_add_right hX1 1
    simpa only [add_comm,show (1:V)+1=2 by ring] using hh
  have hA4 : (4:V)≤AA := calc
    4=2*2 := by ring
    _≤(mu p v*Y p v)*(X p v+1) := mul_le_mul hS2 hXplus (by simp) (by simp)
  have hD : (16:V)≤D := calc
    16≤4*(4+2) := by norm_num
    _≤AA*(AA+2) := mul_le_mul hA4 (by simpa only [add_comm] using add_le_add_right hA4 2) (by simp) (by simp)
  have hi : 1≤v 3 := pos_iff_one_le.mp (hv 3)
  have hU : C≤U0 := calc
    C≤C*C := le_mul_of_one_le_right (by simp) hc1
    _≤v 3*(C*C) := le_mul_of_one_le_left (by simp) hi
  have ht1 : 1≤tau := pos_iff_one_le.mp ht
  change E0=tau*tau at hE
  have ha : D*U0*U0*tau*tau=a := by
    calc
      D*U0*U0*tau*tau=(D*U0*U0)*(tau*tau) := by ring
      _=(D*U0*U0)*E0 := by rw [hE]
      _=a := by rfl
  have hfs : f*f=1+D*U0*U0*tau*tau := by
    calc
      f*f=1+a := hf2.symm
      _=1+D*U0*U0*tau*tau := by rw [ha]
  obtain ⟨hcB,hcF,htfF⟩ := CarrierSizes.sufficient D U0 tau f C hD hc1 hU ht1 hfs
  change C<D*(4*(D*U0*U0*tau*tau)*(1+D*U0*U0*tau*tau))-1 at hcB
  change 2*C<1+2*(D*U0*U0*tau*tau) at hcF
  change 8*tau*f≤1+2*(D*U0*U0*tau*tau) at htfF
  rw [ha] at hcB hcF htfF
  change C<Q-1 at hcB
  have hB : 0<Q-1 := lt_of_le_of_lt (by simp) hcB
  have hQpos : 0<Q := lt_of_lt_of_le hB tsub_le_self
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQpos)
  have hnorm : (1+(Q-1))*(V0*V0)=1+(Q-1)*(y*y) := by
    rw [add_comm,hQ1]
    exact haux
  have hsign := graph_signed_residue p v V0 hVs
  change ArithmeticPellHalfIndex.SignMod F V0 C at hsign
  have hbound := Direct80CarrierEstimate.adjacent_carrier_bound (Q-1) F C V0 y tau f
    hB hcB hcgt hV ht hf hnorm hsign hcF htfF
  exact hbound

#print axioms Direct80GraphCarrierParam.bound_for_witnesses
end Direct80GraphCarrierParam
