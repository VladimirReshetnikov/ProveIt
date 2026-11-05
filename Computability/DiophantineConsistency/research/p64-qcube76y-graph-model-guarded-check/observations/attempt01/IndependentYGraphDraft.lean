import P64QCube76Y
import P64QCube77Unit
import IndependentYBounds

/-! Unchecked draft: graph-level split and norm extraction for independent y. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace IndependentYGraphDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open P64QCubeMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_same (p : Fin 4 → ℤ) : (P64QCube76Y.graph p).A0=(P64QCube78.graph p).A0 := by rfl
theorem main_same (p : Fin 4 → ℤ) : (P64QCube76Y.graph p).M=(P64QCube81.graph p).M := by rfl
theorem strong_same (p : Fin 4 → ℤ) : (P64QCube76Y.graph p).W=(P64QCube81.graph p).W := by rfl
theorem transport_same (p : Fin 4 → ℤ) : (P64QCube76Y.graph p).Lt=(P64QCube78.graph p).Lt := by rfl

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube76Y.graph p).output =
    ((P64QCube76Y.graph p).A0*(P64QCube76Y.graph p).Na-1)*
      ((P64QCube76Y.graph p).A0*(P64QCube76Y.graph p).Na-1)+
    (P64QCube76Y.graph p).M*(P64QCube76Y.graph p).M+
    (P64QCube76Y.graph p).W*(P64QCube76Y.graph p).W+
    (P64QCube76Y.graph p).Lt*(P64QCube76Y.graph p).Lt := by rfl

theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    let g := P64QCube76Y.graph (fun j => (p j:ℤ))
    let z : Fin 14 → DiffRing V := fun i => ι (v i)
    g.A0.evalRing z=1 ∧ g.M.evalRing z=0 ∧ g.W.evalRing z=0 ∧
      g.Na.evalRing z=1 ∧ g.Lt.evalRing z=0 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let g := P64QCube76Y.graph pp
  let a := g.A0.evalRing z
  let m := g.M.evalRing z
  let w := g.W.evalRing z
  let n := g.Na.evalRing z
  let l := g.Lt.evalRing z
  have hs : (a*n-1)*(a*n-1)+m*m+w*w+l*l=0 := by
    rw [internalZero_iff,output_shape] at hz
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat] at hz
    exact hz
  have hu := mul_self_nonneg (a*n-1)
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hl := mul_self_nonneg l
  have hunit : a*n=1 := sub_eq_zero.mp (mul_self_eq_zero.mp (by linarith))
  have hm0 : m=0 := mul_self_eq_zero.mp (by linarith)
  have hw0 : w=0 := mul_self_eq_zero.mp (by linarith)
  have hl0 : l=0 := mul_self_eq_zero.mp (by linarith)
  have hlt : InternalZero (P64QCube78.graph pp).Lt v := by
    rw [internalZero_iff,←transport_same pp]
    exact hl0
  have haneg : a≠ -1 := by
    change (P64QCube76Y.graph pp).A0.evalRing z≠ -1
    rw [first_same pp]
    exact P64QCube77Unit.first_ne_neg_of_transport p v hv hlt
  obtain ⟨ha,hn⟩ := P64QCube77Unit.positive_factors hunit haneg
  exact ⟨ha,hm0,hw0,hn,hl0⟩

theorem main_root (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := (q*q*q)*v 7
    let X := v 8*q
    let a := X*Y+Y
    let c := (v 10+v 11)*Y+v 10
    ∃g : V, g*g=(a*a+(4*a+3))*(c*c)+1 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let w : Fin 14 → V := lift p v
  let q : V := (p 0:V)*v 0+1
  obtain ⟨_,hm,_,_,hl⟩ := residuals p v hv hz
  have hmain : InternalZero (P64Graph.graph pp).M w := by
    rw [internalZero_iff]
    change (P64QCube76Y.graph pp).M.evalRing z=0 at hm
    rw [main_same pp,←P64QCubeBinding.main pp z,←P64QCubeMap.lift_cast p v] at hm
    exact hm
  have hlt : InternalZero (P64Graph.graph pp).Lt w := by
    rw [internalZero_iff]
    change (P64QCube76Y.graph pp).Lt.evalRing z=0 at hl
    rw [transport_same pp,P64QCube78GraphSplit.transport_same pp,
      ←P64QCubeBinding.transport pp z,←P64QCubeMap.lift_cast p v] at hl
    exact hl
  have hwp := P64QCubeMap.lift_pos p v hv
  have hgap := (P64Root.transport p w hwp hlt).1
  have hb : 0<(p 0:V) := by
    by_contra hn
    have he : (p 0:V)=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [he,zero_mul,zero_add] at hgap
    have hone : 1≤w 1+w 2 := pos_iff_one_le.mp (add_pos (hwp 1) (hwp 2))
    exact (not_lt_of_ge hone) hgap
  have hF : w 1≤(p 0:V)*w 0+1 := le_trans (by simp) (le_of_lt hgap)
  have hYdiv : ((p 0:V)*w 0+1)*((p 0:V)*w 0+1)*((p 0:V)*w 0+1) ∣ w 7 := by
    refine ⟨v 7,?_⟩
    simp [w,lift]
  obtain ⟨g,hg,_⟩ := P64Root.main_root p w hwp hb hF hYdiv hmain
  refine ⟨g,?_⟩
  simpa [w,lift,q] using hg

#print axioms IndependentYGraphDraft.residuals
#print axioms IndependentYGraphDraft.main_root
end IndependentYGraphDraft
