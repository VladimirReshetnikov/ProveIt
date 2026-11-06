import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.ModelDifferenceRing

/-! Model scalar and first-index windows with the draft's full hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33Windows
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellFirstIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem windows_from_maintained_norms
    (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hbeta : 0<beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (hgamma : 0<gamma) :
    let q:=beta*J+1
    let X:=w*q
    let Y:=s*q^3
    let E:=X*Y
    let k:=eta+zeta
    let c:=k*Y+eta
    let a:=E+Y
    let d:=X+a*c+gamma*(4*a+3)
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let tau:=E*N+k-R
    let I:=delta a*i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k →
    d*d=1+delta a*c*c →
    f*f=1+delta a*(i*c*c)*(i*c*c) →
    I*I*u*u+y*y=1+I*I*y*y →
    0<q-F-alpha ∧ R+2<E ∧ 2*R<c := by
  dsimp only
  intro htransport hfirst hmain hstrict haux
  let q:=beta*J+1
  let E:=(w*q)*(s*q^3)
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let c:=(eta+zeta)*(s*q^3)+eta
  obtain ⟨hgap, _, hRsmall⟩ := scalar_window q beta K MC MF J F alpha z w s
    hbeta hJ hF halpha hz hw hs hMC hMF rfl htransport
  have hE : w*s*q^4=E := by dsimp [E]; ring
  rw [hE] at hRsmall
  obtain ⟨n,h,hn5,hnR,hnrel,htau,hk,hd,hc,hbig,hhalf,hpos,hfinal⟩ :=
    maintained_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma
      hbeta hMC hMF hJ hF halpha hz hf hi hT hs hw hN heta hzeta hy hgamma
      htransport hfirst hmain hstrict haux
  exact ⟨hgap,hRsmall,hhalf⟩
end DiophantineConsistency.Sign33Windows
#print axioms DiophantineConsistency.Sign33Windows.windows_from_maintained_norms
