import Absorb89FirstQuotient
import DiophantineConsistency.ArithmeticAdaptiveTransport2011

/-! First-factor transport for the direct-main graph draft. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb89Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89 Absorb89First Absorb89FirstQuotient
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveTransport2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Reduced first root as a signed difference with nonnegative pieces. -/
theorem root_rep (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let ell : V := (X*Y)*(Y*k)
    let W : V := 1+k*b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    Equivalent (pairEval (firstParts (integerPorts p)).1 v)
      (b*(ell+k+v 7)+Bn*(W*q),Bp*(W*q)) := by
  let eB : Expr (Fin 12) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 12) := .add (.constant 1) eB
  let eQ3 : Expr (Fin 12) := .mul eQ (.mul eQ eQ)
  let eX : Expr (Fin 12) := .mul eQ (.var 5)
  let eY : Expr (Fin 12) := .mul eQ3 (.var 6)
  let eK : Expr (Fin 12) := .add (.var 8) (.var 9)
  let eL : Expr (Fin 12) := .mul (.mul eX eY) (.mul eY eK)
  let eC : Expr (Fin 12) := .sub (.sub eQ (.var 1)) (.var 2)
  let eA : Expr (Fin 12) := .add (.constant (p 1)) (.var 5)
  let eBt : Expr (Fin 12) := .mul eQ (.sub (.mul eC eA) (.var 1))
  let eZ : Expr (Fin 12) := .sub
    (.mul eB (.sub (.add (.add eL eK) (.var 7)) (.mul eK eBt))) eBt
  change Equivalent (pairEval eZ v) _
  simp [eZ,eBt,eA,eC,eL,eK,eY,eX,eQ3,eQ,eB,pairEval,Expr.splitNatural,
    NatExpr.evalSemiring,Equivalent]
  all_goals ring

/-- Positive witnesses and beta force the transport gap in every model. -/
theorem transport (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let q : V := 1+v 0*(p 0:V)
    let A : V := (p 1:V)+v 5
    (v 1+v 2)*A+v 1 < q*A ∧ 0<q-(v 1+v 2) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let ell : V := (X*Y)*(Y*k)
  let W : V := 1+k*b
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let zp : Pair V := (b*(ell+k+v 7)+Bn*(W*q),Bp*(W*q))
  let z := pairEval (firstParts (integerPorts p)).1 v
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hq : 0<q := by dsimp [q,b]; simp
  have hk : 0<k := add_pos (hv 8) (hv 9)
  have hX : 0<X := mul_pos hq (hv 5)
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have he : 0<ell := mul_pos (mul_pos hX hY) (mul_pos hY hk)
  obtain ⟨t,htpos,ht,hn⟩ := first_root p v hz hb0
  have hn' : t*t=1+ell*(ell+k) := by
    calc
      t*t=1+((X*Y)*Y)*(((X*Y)*Y)+1)*k*k := hn
      _=1+ell*(ell+k) := by dsimp [ell]; ring
  have hbound : t<ell+k := first_root_bound ell k t he hk hn'
  have hmag : magnitude z=magnitude zp := magnitude_equivalent (root_rep p v)
  have hBt : Bn<Bp := by
    by_contra hnle
    have hle : Bp≤Bn := le_of_not_gt hnle
    let u := Bn-Bp
    have hu : Bn=Bp+u := by rw [add_comm,tsub_add_cancel_of_le hle]
    have heq : zp.1=zp.2+(b*(ell+k+v 7)+u*(W*q)) := by
      dsimp only [zp]
      rw [hu]
      ring
    have hmagZ : magnitude zp=b*(ell+k+v 7)+u*(W*q) := magnitude_of_add heq
    have hscale : b*(ell+k+v 7)≤b*t := calc
      _≤b*(ell+k+v 7)+u*(W*q) := by simp
      _=magnitude zp := hmagZ.symm
      _=magnitude z := hmag.symm
      _=b*t := ht
    have hbound' : ell+k+v 7≤t := le_of_mul_le_mul_left hscale hb0
    have hle' : ell+k≤t := le_trans (by simp) hbound'
    exact (not_lt_of_ge hle') hbound
  have hgap : v 1+v 2<q := by
    by_contra hn
    have hle : q≤v 1+v 2 := le_of_not_gt hn
    have hle' : Bp≤Bn := calc
      q*A≤(v 1+v 2)*A := mul_le_mul_of_nonneg_right hle (by simp)
      _≤(v 1+v 2)*A+v 1 := by simp
    exact (not_le_of_gt hBt) hle'
  exact ⟨hBt,tsub_pos_iff_lt.mpr hgap⟩

#print axioms Absorb89Transport.root_rep
#print axioms Absorb89Transport.transport
end Absorb89Transport
