import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

/-! Actual first-root bounds force the signed transport to be positive.
No orientation of the first root is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveTransport2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFirstDivisibility2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem difference_equal (x y u v : V) (h : x+v=y+u) : x-y=u-v := by
  calc
    x-y=(x+v)-(y+v) := (add_tsub_add_eq_tsub_right x v y).symm
    _=(y+u)-(y+v) := by rw [h]
    _=u-v := by rw [add_comm y u,add_comm y v,add_tsub_add_eq_tsub_right]

/-- Equivalent formal differences have the same natural magnitude. -/
theorem magnitude_equivalent {p q : Pair V} (h : Equivalent p q) : magnitude p=magnitude q := by
  have h1 : p.1-p.2=q.1-q.2 := difference_equal _ _ _ _ h
  have h2 : p.2-p.1=q.2-q.1 := difference_equal _ _ _ _ h.symm
  simp only [magnitude,h1,h2]

/-- A positive first Pell norm has strictly smaller root than ell+k. -/
theorem first_root_bound (ell k t : V) (he : 0<ell) (hk : 0<k)
    (hn : t*t=1+ell*(ell+k)) : t<ell+k := by
  have hp : 1≤ell*k := one_le_mul (pos_iff_one_le.mp he) (pos_iff_one_le.mp hk)
  have hq : 1≤k*k := one_le_mul (pos_iff_one_le.mp hk) (pos_iff_one_le.mp hk)
  have htwo : (2:V)≤ell*k+k*k := by simpa only [one_add_one_eq_two] using add_le_add hp hq
  have hs : (1:V)<ell*k+k*k := lt_of_lt_of_le (by simp : (1:V)<2) htwo
  have hsq : t*t<(ell+k)*(ell+k) := calc
    t*t=1+ell*(ell+k) := hn
    _<(ell*k+k*k)+ell*(ell+k) := by simpa only [add_comm] using add_lt_add_right hs (ell*(ell+k))
    _=(ell+k)*(ell+k) := by ring
  exact lt_of_mul_self_lt_mul_self₀ (by simp) hsq

def TransportPositive (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let A : V := v 6+(p 1:V)*q
  (v 1+v 2)*A+v 1*q < q*A ∧ 0<q-(v 1+v 2)

/-- The actual quotient and norm force the actual signed transport positive. -/
theorem quotients_force_transport (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (h : Quotients p v) : TransportPositive p v := by
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
  let zp : Pair V := (M*(ell+k+v 8)+v 7*b+Bn*(W*Q),Bp*(W*Q))
  let z := pairEval (rootTerm (factors (fun j => (p j:ℤ))).1) v
  have hp := scaled_parameters_positive p v hb hv
  have hM : 0<M := hp.2.1
  have hk : 0<k := hp.2.2.2.1
  have he : 0<ell := hp.2.2.2.2
  obtain ⟨t,d,_,_,ht,hn,_,_⟩ := h
  have hbound : t<ell+k := first_root_bound ell k t he hk hn
  have hmag : magnitude z=magnitude zp := magnitude_equivalent (first_root_rep p v)
  have hBt : Bn<Bp := by
    by_contra hnle
    have hle : Bp≤Bn := le_of_not_gt hnle
    let u := Bn-Bp
    have hu : Bn=Bp+u := by rw [add_comm,tsub_add_cancel_of_le hle]
    have heq : zp.1=zp.2+(M*(ell+k+v 8)+v 7*b+u*(W*Q)) := by
      dsimp only [zp]
      rw [hu]
      ring
    have hmagZ : magnitude zp=M*(ell+k+v 8)+v 7*b+u*(W*Q) := magnitude_of_add heq
    have hscale : M*(ell+k+v 8)≤M*t := calc
      _≤M*(ell+k+v 8)+v 7*b+u*(W*Q) := by simp
      _=magnitude zp := hmagZ.symm
      _=magnitude z := hmag.symm
      _=M*t := ht
    have hbound' : ell+k+v 8≤t := le_of_mul_le_mul_left hscale hM
    have hle' : ell+k≤t := le_trans (by simp) hbound'
    exact (not_lt_of_ge hle') hbound
  have hgap : v 1+v 2<q := by
    by_contra hn
    have hle : q≤v 1+v 2 := le_of_not_gt hn
    have hle' : Bp≤Bn := calc
      q*A≤(v 1+v 2)*A := mul_le_mul_of_nonneg_right hle (by simp)
      _≤(v 1+v 2)*A+v 1*q := by simp
    exact (not_le_of_gt hBt) hle'
  exact ⟨hBt,tsub_pos_iff_lt.mpr hgap⟩

theorem expressionAt_transport_positive (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : TransportPositive p v :=
  quotients_force_transport p v hb hv (expressionAt_quotients p v hb hv hz)

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_transport_positive (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : TransportPositive currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_transport_positive currentPorts v hp hv
  rw [currentPorts_cast]
  exact hz

theorem current_natural_transport_positive (v : Fin 13 → V)
    (hz : InternalZero naturalExpression v) : TransportPositive currentPorts (fun j => v j+1) :=
  current_transport_positive _
    (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)

end DiophantineConsistency.ArithmeticAdaptiveTransport2011
