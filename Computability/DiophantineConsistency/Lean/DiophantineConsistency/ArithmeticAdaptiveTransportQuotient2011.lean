import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! The literal first-root quotient also gives a positive transport quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive literal transport is a positive multiple of the actual b=q−1. -/
def TransportQuotient (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let A : V := v 6+(p 1:V)*q
  ∃ w : V, 0<w ∧ q*A=(v 1+v 2)*A+v 1*q+b*w

theorem quotient_transport (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hM : 0<(1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))
    (hB : TransportPositive p v)
    (t : V)
    (ht : magnitude (pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v) =
      ((1+v 0*(p 0:V))*((1+v 0*(p 0:V))*(1+v 0*(p 0:V)))*(v 0*(p 0:V)))*t) :
    TransportQuotient p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 6+(p 1:V)*q
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1*q
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v
  have hb : 0<b := pos_of_mul_pos_right hM (by simp)
  have hdiv : M∣magnitude z := ⟨t,ht⟩
  have hzmod := magnitude_mod z M hM hdiv
  have hpair := equivalent_mod hM (first_root_rep p v) hzmod
  change (M*(ell+k+v 8)+v 7*b+Bn*(W*Q))%M = (Bp*(W*Q))%M at hpair
  have hdbM : b∣M := ⟨Q,by dsimp only [M]; ring⟩
  have hbpair := congrArg (fun x : V => x%b) hpair
  rw [mod_mod_dvd hb hdbM,mod_mod_dvd hb hdbM] at hbpair
  let T : V := q*q+q+1
  let H : V := k+T+k*b*T
  have hQ : Q=1+b*T := by dsimp [Q,q,T]; ring
  have hWQ : W*Q=1+b*H := by dsimp only [W,H]; rw [hQ]; ring
  have hleft : M*(ell+k+v 8)+v 7*b+Bn*(W*Q) =
      Bn+b*(Q*(ell+k+v 8)+v 7+Bn*H) := by dsimp only [M]; rw [hWQ]; ring
  have hright : Bp*(W*Q)=Bp+b*(Bp*H) := by rw [hWQ]; ring
  rw [hleft,hright,mod_add_mul' _ _ hb,mod_add_mul' _ _ hb] at hbpair
  have hpos : Bn<Bp := hB.1
  have hd : b∣Bp-Bn := congruence_divides_difference hb (le_of_lt hpos) hbpair.symm
  obtain ⟨w,hw⟩ := hd
  have hwp : 0<w := pos_of_mul_pos_right (by rw [←hw]; exact tsub_pos_iff_lt.mpr hpos) (by simp)
  have hfinal : Bp=Bn+b*w := by
    have he := tsub_add_cancel_of_le (le_of_lt hpos)
    rw [hw] at he
    simpa only [add_comm] using he.symm
  exact ⟨w,hwp,hfinal⟩

theorem expressionAt_transport_quotient (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : TransportQuotient p v := by
  have hp := scaled_parameters_positive p v hb hv
  obtain ⟨t,d,_,_,ht,_,_,_⟩ := expressionAt_quotients p v hb hv hz
  exact quotient_transport p v hp.2.1 (expressionAt_transport_positive p v hb hv hz) t ht

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_transport_quotient (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : TransportQuotient currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_transport_quotient currentPorts v hp hv
  rw [currentPorts_cast]
  exact hz

theorem current_natural_transport_quotient (v : Fin 13 → V)
    (hz : InternalZero naturalExpression v) : TransportQuotient currentPorts (fun j => v j+1) :=
  current_transport_quotient _
    (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011
