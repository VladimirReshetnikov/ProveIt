import DiophantineConsistency.FreeJRootBinding
import DiophantineConsistency.ArithmeticAdaptiveTransport2011
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJFirstTransport
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveQuotients2011
open DiophantineConsistency.ArithmeticAdaptiveTransport2011
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem freej_first_factor_transport (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let A : V := v 5+(p 1:V)*q
    (v 1+v 2)*A+v 1*q < q*A ∧ 0<q-(v 1+v 2) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let Q : V := q*(q*q)
  let k : V := v 8+v 9
  let ell : V := (v 5*v 6)*(v 6*k)
  let M : V := Q*b
  let W : V := 1+k*b
  let A : V := v 5+(p 1:V)*q
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1*q
  let zp : Pair V := (M*(ell+k+v 7)+v 6*b+Bn*(W*Q),Bp*(W*Q))
  let z := pairEval (core (fun j => (p j:ℤ))).z v
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q,b]; simp
  have hM : 0<M := mul_pos (mul_pos hq (mul_pos hq hq)) hb0
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have he : 0<ell := mul_pos (mul_pos (hv 5) (hv 6)) (mul_pos (hv 6) hk)
  obtain ⟨t,ht,hn⟩ := scaled_quotient _ _ _ hM (first_scaled_norm p v hz)
  have hbound : t<ell+k := first_root_bound ell k t he hk hn
  have hmag : magnitude z=magnitude zp := magnitude_equivalent (root_rep p v)
  have hBt : Bn<Bp := by
    by_contra hnle
    have hle : Bp≤Bn := le_of_not_gt hnle
    let u := Bn-Bp
    have hu : Bn=Bp+u := by rw [add_comm,tsub_add_cancel_of_le hle]
    have heq : zp.1=zp.2+(M*(ell+k+v 7)+v 6*b+u*(W*Q)) := by
      dsimp only [zp]
      rw [hu]
      ring
    have hmagZ : magnitude zp=M*(ell+k+v 7)+v 6*b+u*(W*Q) := magnitude_of_add heq
    have hscale : M*(ell+k+v 7)≤M*t := calc
      _≤M*(ell+k+v 7)+v 6*b+u*(W*Q) := by simp
      _=magnitude zp := hmagZ.symm
      _=magnitude z := hmag.symm
      _=M*t := ht
    have hbound' : ell+k+v 7≤t := le_of_mul_le_mul_left hscale hM
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


end FreeJFirstTransport
#print axioms FreeJFirstTransport.freej_first_factor_transport
