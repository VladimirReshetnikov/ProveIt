import DiophantineConsistency.ArithmeticAdaptiveRadix2011

/-! Restore the normalized transport quotient from the actual adaptive zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransportQuotient2011 ArithmeticAdaptiveRadix2011
open ArithmeticGcdNormalization ArithmeticPellStrongDivisibility
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def RestoredTransport (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  ∃ w z : V, 0<w ∧ 0<z ∧ v 6=q*w ∧
    q*((CurrentKernel2011.K:V)+w)=(v 1+v 2)*((CurrentKernel2011.K:V)+w)+v 1+(q-1)*z

theorem current_transport_restoration (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : Radix v ∧ RestoredTransport v := by
  let q : V := 1+v 0*(CurrentMasks2011.beta:V)
  let X : V := v 6
  let K : V := (CurrentKernel2011.K:V)
  let A : V := X+K*q
  have hrad := current_radix v hv hz
  obtain ⟨N,w,hN,hqN,hNR,hwexp,hX,hexp1,hexp2⟩ := hrad
  have hw : 0<w := by rw [hwexp]; exact exp_pos _
  have hqgt : 1<q := (current_parameters_positive v hv).1
  have hq : 0<q := lt_trans (by simp : (0:V)<1) hqgt
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (le_of_lt hqgt)
  have hbq : q-1=v 0*(CurrentMasks2011.beta:V) := by dsimp [q]; rw [add_comm]; simp
  obtain ⟨j,hj,hjt⟩ := current_transport_quotient v hv hz
  change q*A=(v 1+v 2)*A+v 1*q+(v 0*(CurrentMasks2011.beta:V))*j at hjt
  rw [←hbq] at hjt
  have hA : A=q*(K+w) := by dsimp [A,X]; rw [hX]; ring
  have hd1 : q∣(v 1+v 2)*A+v 1*q := by
    refine ⟨(v 1+v 2)*(K+w)+v 1,?_⟩
    rw [hA]; ring
  have hd2 : q∣((q-1)*j)+((v 1+v 2)*A+v 1*q) := by
    refine ⟨A,?_⟩
    rw [hjt]; ring
  have hd : q∣(q-1)*j := dvd_remove hd2 hd1
  have hbez : Bez (q-1) q 1 := by
    refine ⟨1,0,0,1,?_⟩
    simp only [mul_one,mul_zero,add_zero]
    rw [add_comm,hq1]
  have hjdiv : q∣j := unit_certificate_cancel hbez hd
  obtain ⟨z,hjz⟩ := hjdiv
  have hzpos : 0<z := pos_of_mul_pos_right (by rw [←hjz]; exact hj) (by simp)
  have ht : q*(K+w)=(v 1+v 2)*(K+w)+v 1+(q-1)*z := by
    apply mul_left_cancel₀ (ne_of_gt hq)
    calc
      q*(q*(K+w))=q*A := by rw [hA]
      _=(v 1+v 2)*A+v 1*q+(q-1)*j := hjt
      _=q*((v 1+v 2)*(K+w)+v 1+(q-1)*z) := by rw [hA,hjz]; ring
  refine ⟨⟨N,w,hN,hqN,hNR,hwexp,hX,hexp1,hexp2⟩,?_,?_,?_,?_,?_⟩
  exact ⟨w,z,hw,hzpos,hX,ht⟩

theorem current_natural_transport_restoration (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    Radix (fun j => v j+1) ∧ RestoredTransport (fun j => v j+1) :=
  current_transport_restoration _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
