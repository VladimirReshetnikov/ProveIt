import DiophantineConsistency.ArithmeticPellPowerRecovery

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellPowerRecoveryChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a : V) : xcoord 0 a=Exp.exp 0+a*ycoord 0 a+(4*a+3)*0 := by simp

example (a b : V) : Exp.exp (4*0)*ycoord (0+1) b=ycoord (2*0+1) a := by
  have hy (b : V) : ycoord 1 b=1 := by simpa using y_succ (0:V) b
  simp [hy]

/-- The upper step intentionally has no zero-time claim. -/
example (b : V) : ¬ ycoord (0+1) b≤2*(b+2)*ycoord 0 b := by
  have hy : ycoord 1 b=1 := by simpa using y_succ (0:V) b
  simp [hy]

example (a b r : V) (hs : 16*(2*(b+2))<(2*a+3)*(2*a+3)) (hr : 0<r) :
    Exp.exp (4*r)*ycoord (r+1) b<ycoord (2*r+1) a := paired_comparison_strict a b hs r hr

/-- The literal client supplies no first/main index or power premise. -/
example (beta K MC MF J F alpha z f i T s w N eta zeta y gamma : V)
    (hb : 15≤beta) (hMC : MC<beta) (hMF : MF<2*beta)
    (hJ : 0<J) (hF : 0<F) (halpha : 0<alpha) (hz : 0<z)
    (hf : 0<f) (hi : 0<i) (hT : 0<T) (hs : 0<s) (hw : 0<w)
    (hN : 0<N) (heta : 0<eta) (hzeta : 0<zeta) (hy : 0<y) (hgamma : 0<gamma) :
    let q:=beta*J+1; let X:=w*q; let Y:=s*q^3; let E:=X*Y
    let k:=eta+zeta; let c:=k*Y+eta; let a:=E+Y
    let d:=X+a*c+gamma*(4*a+3)
    let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
    let tau:=E*N+k-R; let I:=delta a*i*c*c
    let u:=absdiff (f*f*c*T) (f*f*R+c)
    (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 →
    tau*tau=1+(E*Y)*(E*Y+1)*k*k → d*d=1+delta a*c*c →
    f*f=1+delta a*(i*c*c)*(i*c*c) → I*I*u*u+y*y=1+I*I*y*y →
    Exponential R X := by
  dsimp only
  intro ht hn hm hstrict haux
  exact (maintained_power beta K MC MF J F alpha z f i T s w N eta zeta y gamma
    hb hMC hMF hJ hF halpha hz hf hi hT hs hw hN heta hzeta hy hgamma
    ht hn hm hstrict haux).2.1

#print axioms y_lower
#print axioms y_upper
#print axioms paired_comparison
#print axioms paired_comparison_strict
#print axioms coefficient_gap
#print axioms power_bound
#print axioms projection_quotient
#print axioms power_of_coordinates
#print axioms maintained_power
end DiophantineConsistency.ArithmeticPellPowerRecoveryChecks
