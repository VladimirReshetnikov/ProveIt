import DiophantineConsistency.ArithmeticAdaptiveWindowCore2011
import DiophantineConsistency.ArithmeticAdaptivePortValues2011
import DiophantineConsistency.ArithmeticAdaptivePopulation2011
import DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011

/-! Window assembly from the actual adaptive natural zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveWindow2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveRadix2011 ArithmeticAdaptiveTransportRestoration2011 ArithmeticAdaptivePopulation2011
open ArithmeticWindowInterface ArithmeticBinaryPopulation ArithmeticAdaptiveWindowCore2011
open ArithmeticAdaptivePortValues2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def embedding (v : Fin 13 → V) (z w : V) : Fin 14 → V :=
  ![v 0,v 1,v 2,z+1,1,1,1,1,w,1,1,1,1,1]

theorem current_window (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) :
    ∃ N W C F : V, Window N W C F := by
  let q : V := 1+v 0*(currentPorts 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((currentPorts 2:V)+q*(currentPorts 3:V))*v 0
  obtain ⟨w,z,hw,hzpos,hX,ht⟩ := current_transport_restoration v hv hz
  obtain ⟨L,w',hL,hqN,hLR,hwexp,hX',hgraphq,hgraphw⟩ := current_radix v hv hz
  have hq1 : 1<q := by
    have h := (current_parameters_positive v hv).1
    change 1<1+v 0*(currentPorts 0:V)
    rw [port0_cast]
    exact h
  have hq0 : 0<q := lt_trans (by simp : (0:V)<1) hq1
  have hqpred : q-1+1=q := tsub_add_cancel_of_le (le_of_lt hq1)
  change v 6=q*w at hX
  change v 6=q*w' at hX'
  have hww : w=w' := mul_left_cancel₀ (ne_of_gt hq0) (hX.symm.trans hX')
  rw [←hww] at hwexp hgraphw
  let u : Fin 14 → V := embedding v z w
  have hu : ∀j,0<u j := by
    intro j
    fin_cases j <;> simp [u,embedding,hv,hw,hzpos]
  have hq14 : ArithmeticCarrierRadix2011.q u=q := by
    change (CurrentMasks2011.beta:V)*v 0+1=1+v 0*(currentPorts 0:V)
    rw [port0_cast]
    ring
  have hR14 : ArithmeticCarrierRadix2011.rank u=R := by
    unfold ArithmeticCarrierRadix2011.rank
    rw [hq14]
    change ((q-1)*(q-v 1)+v 2)*(q^2-1)+
      ((CurrentMasks2011.lowPort:V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*v 0=
      ((q-1)*(q-v 1)+v 2)*(q^2-1)+((currentPorts 2:V)+q*(currentPorts 3:V))*v 0
    rw [port2_cast,port3_cast]
  have ht14 : ((CurrentKernel2011.K:V)+u 8)*ArithmeticCarrierRadix2011.q u+ArithmeticCarrierRadix2011.q u =
      ((CurrentKernel2011.K:V)+u 8)*(u 1+u 2)+u 1+u 3*(ArithmeticCarrierRadix2011.q u-1)+1 := by
    change ((CurrentKernel2011.K:V)+w)*ArithmeticCarrierRadix2011.q u+ArithmeticCarrierRadix2011.q u =
      ((CurrentKernel2011.K:V)+w)*(v 1+v 2)+v 1+(z+1)*(ArithmeticCarrierRadix2011.q u-1)+1
    rw [hq14]
    change q*((currentPorts 1:V)+w)=(v 1+v 2)*((currentPorts 1:V)+w)+v 1+(q-1)*z at ht
    rw [port1_cast] at ht
    calc
      ((CurrentKernel2011.K:V)+w)*q+q=q*((CurrentKernel2011.K:V)+w)+q := by ring
      _=((v 1+v 2)*((CurrentKernel2011.K:V)+w)+v 1+(q-1)*z)+(q-1+1) := by rw [ht,hqpred]
      _=((CurrentKernel2011.K:V)+w)*(v 1+v 2)+v 1+(z+1)*(q-1)+1 := by ring
  have hr14 : ArithmeticCarrierRadix2011.Radix u := by
    refine ⟨L,hL,?_,?_,?_,?_,?_⟩
    · rw [hq14]; exact hqN
    · rw [hR14]; exact hLR
    · change w=Exp.exp (ArithmeticCarrierRadix2011.rank u-(CurrentMasks2011.width:V)*L)
      rw [hR14]; exact hwexp
    · rw [hq14]; exact hgraphq
    · change Exponential (ArithmeticCarrierRadix2011.rank u-(CurrentMasks2011.width:V)*L) w
      rw [hR14]; exact hgraphw
  have hσ : ∀ N : V, ArithmeticCarrierRadix2011.q u=Exp.exp (94517*N) →
      3*(94517*N)+2≤population (ArithmeticCarrierRadix2011.rank u) := by
    intro N h
    rw [hq14] at h
    rw [hR14]
    have hp := current_population_at v hv hz (94517*N)
    change q=Exp.exp (94517*N) → 3*(94517*N)+2≤population R at hp
    exact hp h
  obtain ⟨N,_,hwindow⟩ := window_of_transport u hu ht14 hr14 hσ
  exact ⟨N,_,_,_,hwindow⟩

theorem current_natural_window (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ∃ N W C F : V, Window N W C F :=
  current_window _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveWindow2011
