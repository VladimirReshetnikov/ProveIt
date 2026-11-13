import DiophantineConsistency.Compact44.Absorb89Transport

/-! Bind both first-root signs to the speculative graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb89Signs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First Absorb89FirstQuotient Absorb89Transport
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem magnitude_cases (P N M : V) (h : magnitude (P,N)=M) :
    P=N+M ∨ N=P+M := by
  rcases le_total N P with hp | hn
  · have he : P=N+(P-N) := by rw [add_comm,tsub_add_cancel_of_le hp]
    have hm : magnitude (P,N)=P-N := magnitude_of_add he
    left
    rw [←h,hm]
    exact he
  · have he : N=P+(N-P) := by rw [add_comm,tsub_add_cancel_of_le hn]
    have hm : magnitude (N,P)=N-P := magnitude_of_add he
    have hswap : magnitude (P,N)=magnitude (N,P) := by simp [magnitude,add_comm]
    right
    rw [←h,hswap,hm]
    exact he

theorem first_branches (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let Q : V := (X*Y)*Y
    let ell : V := (X*Y)*(Y*k)
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    let Bt : V := q*(Bp-Bn)
    ∃ first : V, 0<first ∧ 0<Bt ∧ first*first=1+Q*(Q+1)*k*k ∧
      (b*(ell+k+v 7)=(1+k*b)*Bt+b*first ∨
       b*(ell+k+v 7)+b*first=(1+k*b)*Bt) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let Q : V := (X*Y)*Y
  let ell : V := (X*Y)*(Y*k)
  let W : V := 1+k*b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let Bt : V := q*(Bp-Bn)
  let zp : Pair V := (b*(ell+k+v 7)+Bn*(W*q),Bp*(W*q))
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q,b]; simp
  have hBt : Bn<Bp := (transport p v hb hv hz).1
  have hB : Bp=Bn+(Bp-Bn) := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hBt)]
  have hBtpos : 0<Bt := mul_pos hq (tsub_pos_iff_lt.mpr hBt)
  obtain ⟨first,hfirst,hroot,hnorm⟩ := first_root p v hz hb0
  have hmag : magnitude zp=b*first := by
    have he := magnitude_equivalent (root_rep p v)
    exact he.symm.trans hroot
  have hN : zp.2=Bn*(W*q)+W*Bt := by
    change Bp*(W*q)=Bn*(W*q)+W*(q*(Bp-Bn))
    calc
      Bp*(W*q)=(Bn+(Bp-Bn))*(W*q) := congrArg (fun x : V => x*(W*q)) hB
      _=Bn*(W*q)+W*(q*(Bp-Bn)) := by ring
  have hs := magnitude_cases zp.1 zp.2 (b*first) hmag
  refine ⟨first,hfirst,hBtpos,hnorm,?_⟩
  rcases hs with hs | hs
  · left
    change b*(ell+k+v 7)=W*Bt+b*first
    have hh : Bn*(W*q)+b*(ell+k+v 7)=Bn*(W*q)+(W*Bt+b*first) := by
      calc
        Bn*(W*q)+b*(ell+k+v 7)=zp.1 := by dsimp only [zp]; ring
        _=zp.2+b*first := hs
        _=Bn*(W*q)+(W*Bt+b*first) := by rw [hN]; ring
    exact add_left_cancel hh
  · right
    change b*(ell+k+v 7)+b*first=W*Bt
    have hh : Bn*(W*q)+(b*(ell+k+v 7)+b*first)=Bn*(W*q)+W*Bt := by
      calc
        Bn*(W*q)+(b*(ell+k+v 7)+b*first)=zp.1+b*first := by dsimp only [zp]; ring
        _=zp.2 := hs.symm
        _=Bn*(W*q)+W*Bt := hN
    exact add_left_cancel hh

#print axioms Absorb89Signs.magnitude_cases
#print axioms Absorb89Signs.first_branches
end Absorb89Signs
