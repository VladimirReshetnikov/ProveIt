import DiophantineConsistency.BFS943.Direct80CarrierIdentity
import DiophantineConsistency.BFS943.Direct80SignedCarrier

/-! The actual carrier implies a projection divisor, without cancellation of two. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80ProjectionDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80SignedCarrier
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cancel_base_square {R : Type*} [CommRing R] (m t x : R)
    (hd : m*t-1∣(m*m)*x) : m*t-1∣x := by
  obtain ⟨s,hs⟩ := hd
  refine ⟨s*(t*t)-(m*t+1)*x,?_⟩
  calc
    x=((m*m)*x)*(t*t)-(m*t-1)*((m*t+1)*x) := by ring
    _=((m*t-1)*s)*(t*t)-(m*t-1)*((m*t+1)*x) := by rw [hs]
    _=(m*t-1)*(s*(t*t)-(m*t+1)*x) := by ring

theorem graph_projection_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let w : Fin 10 → DiffRing V := fun j => ι (v j)
    let h := (hExpr (integerPorts p)).evalRing w
    let H := (HExpr (integerPorts p)).evalRing w
    let k := (KExpr (integerPorts p)).evalRing w
    H∣h*k := by
  obtain ⟨_tau,_f,_V0,_y,z,_ht,_hf,_hV,_hy,_he,_hf2,_hVs,hZ,_hsign,_hzle,_haux⟩ :=
    graph_signed_carrier p v hb hv hz
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let h := (hExpr (integerPorts p)).evalRing w
  let u := (muExpr (integerPorts p)).evalRing w
  let m := u*u
  let H := (HExpr (integerPorts p)).evalRing w
  let B := (BExpr (integerPorts p)).evalRing w
  let k := (KExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  let L := (graph (integerPorts p)).v.evalRing w*(graph (integerPorts p)).v.evalRing w
  let t : DiffRing V := 4*ι (Y p v)*(ι (X p v)+1)
  have hH : H=u*t-1 := by
    dsimp [H,HExpr,u,muExpr,qExpr,hExpr,w,t,Y,X,q,b,integerPorts]
    simp only [Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,Nat.cast_ofNat,
      map_mul,map_add,map_one,map_natCast]
    ring
  have hM : (graph (integerPorts p)).m.evalRing w=h*m*H := m_eval (integerPorts p) w
  have hZ' : (graph (integerPorts p)).z.evalRing w=h*m*H*z := by
    rw [M_eval p v hb hv] at hM
    rw [hM] at hZ
    exact hZ
  have hcar : (graph (integerPorts p)).z.evalRing w=h*m*(H*(w 7-L*B)+k)-H*(m*B+h*e) :=
    z_eval (integerPorts p) w
  rw [hZ'] at hcar
  have hdiv : H∣(u*u)*(h*k) := by
    refine ⟨h*m*z-h*m*(w 7-L*B)+m*B+h*e,?_⟩
    dsimp [m]
    linear_combination -hcar
  change H∣h*k
  rw [hH] at hdiv ⊢
  exact cancel_base_square u t (h*k) hdiv

#print axioms TenPositive80ProjectionDivisibility.graph_projection_divisibility
end TenPositive80ProjectionDivisibility
