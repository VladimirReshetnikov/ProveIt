import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! A necessary positive transport inequality for the actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransport2011 AdaptiveGap85FirstDivisibility
open AdaptiveGap85Literal AdaptiveGap85Quotients
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive 85 zero forces `F*q < C*(X+K*q)`, with no sign assumed for its first root. -/
theorem expressionAt_transport85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    v 1*(1+v 0*(p 0:V)) < v 2*(v 6+(p 1:V)*(1+v 0*(p 0:V))) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 6+(p 1:V)*q
  let Bp : V := v 2*A
  let Bn : V := v 1*q
  let zp : Pair V := (M*(ell+k+v 8)+v 7*b+Bn*(W*Q),Bp*(W*Q))
  let z := pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v
  have hp := scaled_parameters_positive p v hb hv
  have hM : 0<M := hp.2.1
  have hk : 0<k := hp.2.2.2.1
  have he : 0<ell := hp.2.2.2.2
  obtain ⟨t,d,_,_,ht,hn,_,_⟩ := expressionAt_quotients85 p v hb hv hz
  have hbound : t<ell+k := first_root_bound ell k t he hk hn
  have hmag : magnitude z=magnitude zp := magnitude_equivalent (first_root_rep85 p v)
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
  exact hBt
end DiophantineConsistency.AdaptiveGap85Transport
