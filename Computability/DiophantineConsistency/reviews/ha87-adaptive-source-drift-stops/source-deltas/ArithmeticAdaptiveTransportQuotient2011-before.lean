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

private theorem mod_cancel {a b c m : V} (hm : 0<m) (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  have hr := le_of_lt (mod_lt c hm)
  have hc : c+(m-c%m)=m*(c/m+1) := by
    calc
      c+(m-c%m)=(m*(c/m)+c%m)+(m-c%m) := by rw [div_add_mod]
      _=m*(c/m)+(c%m+(m-c%m)) := by ring
      _=m*(c/m)+m := by rw [add_tsub_cancel_of_le hr]
      _=m*(c/m+1) := by ring
  have hh : ((a+c)+(m-c%m))%m=((b+c)+(m-c%m))%m := by
    rw [mod_add (a:=a+c) hm,mod_add (a:=b+c) hm,h]
  simpa only [add_assoc,hc,mod_add_mul' _ _ hm] using hh

private theorem magnitude_mod (p : Pair V) (m : V) (hm : 0<m)
    (hd : m∣magnitude p) : p.1%m=p.2%m := by
  have hz : magnitude p%m=0 := mod_eq_zero_iff_dvd.mpr hd
  rcases le_total p.2 p.1 with h|h
  · have he : p.1=p.2+(p.1-p.2) := by rw [add_comm,tsub_add_cancel_of_le h]
    have hg := magnitude_of_add he
    have hs : (p.1-p.2)%m=0 := by rw [←hg]; exact hz
    rw [he,mod_add hm,hs,add_zero,mod_eq_self_of_lt (mod_lt _ hm)]
  · have he : p.2=p.1+(p.2-p.1) := by rw [add_comm,tsub_add_cancel_of_le h]
    have hg : magnitude p=p.2-p.1 := by
      have h' := magnitude_of_add he
      change magnitude (swap p)=p.2-p.1 at h'
      simpa only [magnitude_swap] using h'
    have hs : (p.2-p.1)%m=0 := by rw [←hg]; exact hz
    rw [he,mod_add hm,hs,add_zero,mod_eq_self_of_lt (mod_lt _ hm)]

private theorem equivalent_mod {p q : Pair V} {m : V} (hm : 0<m)
    (he : Equivalent p q) (hp : p.1%m=p.2%m) : q.1%m=q.2%m := by
  have hh := congrArg (fun t : V => t%m) he
  change (p.1+q.2)%m=(p.2+q.1)%m at hh
  rw [mod_add (a:=p.1) (b:=q.2) hm,mod_add (a:=p.2) (b:=q.1) hm,←hp] at hh
  have hh' : (q.2+p.2)%m=(q.1+p.2)%m := by
    rw [mod_add (a:=q.2) (b:=p.2) hm,mod_add (a:=q.1) (b:=p.2) hm,←hp]
    simpa only [add_comm] using hh
  exact (mod_cancel hm hh').symm

private theorem mod_mod_dvd {m n : V} (hm : 0<m) (h : m∣n) (a : V) :
    a%n%m=a%m := by
  conv_rhs => rw [← div_add_mod a n]
  rw [mod_add_remove_left_of_dvd (dvd_mul_of_dvd_left h _) hm]

private theorem congruence_divides_difference {x y m : V} (hm : 0<m)
    (hyx : y≤x) (h : x%m=y%m) : m∣x-y := by
  apply mod_eq_zero_iff_dvd.mp
  have he : x-y+y=x := tsub_add_cancel_of_le hyx
  have hh : ((x-y)+y)%m=(0+y)%m := by
    rw [he,zero_add]
    exact h
  have hc := mod_cancel hm hh
  simpa only [zero_mod] using hc

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
