import Direct80CarrierIdentity
import Direct80SignedCarrier

/-! Actual carrier zero supplies a difference-ring divisibility certificate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80CarrierDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80SignedCarrier
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_carrier_divisibility (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let w : Fin 10 → DiffRing V := fun j => ι (v j)
    let h := (hExpr (integerPorts p)).evalRing w
    let m := (muExpr (integerPorts p)).evalRing w*(muExpr (integerPorts p)).evalRing w
    let H := (HExpr (integerPorts p)).evalRing w
    let e := (eExpr (integerPorts p)).evalRing w
    m∣h*H*e := by
  obtain ⟨tau,f,V0,y,z,_ht,_hf,_hV,_hy,_he,_hf2,_hVs,hZ,_hsign,_hzle,_haux⟩ :=
    graph_signed_carrier p v hb hv hz
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let h := (hExpr (integerPorts p)).evalRing w
  let m := (muExpr (integerPorts p)).evalRing w*(muExpr (integerPorts p)).evalRing w
  let H := (HExpr (integerPorts p)).evalRing w
  let B := (BExpr (integerPorts p)).evalRing w
  let k := (KExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  let L := (graph (integerPorts p)).v.evalRing w*(graph (integerPorts p)).v.evalRing w
  have hM : (graph (integerPorts p)).m.evalRing w=h*m*H := m_eval (integerPorts p) w
  have hZ' : (graph (integerPorts p)).z.evalRing w=h*m*H*z := by
    rw [M_eval p v hb hv] at hM
    rw [hM] at hZ
    exact hZ
  have hcar : (graph (integerPorts p)).z.evalRing w=h*m*(H*(w 7-L*B)+k)-H*(m*B+h*e) :=
    z_eval (integerPorts p) w
  rw [hZ'] at hcar
  refine ⟨h*(H*(w 7-L*B)+k)-H*B-h*H*z,?_⟩
  linear_combination hcar

#print axioms TenPositive80CarrierDivisibility.graph_carrier_divisibility
end TenPositive80CarrierDivisibility
