import DiophantineConsistency.AdaptiveGap85ShiftMainInput

/-! Signed first-root input in arbitrary arithmetic models. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ShiftFirstInput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011 ArithmeticSignedPairExpressions
open AdaptiveGap85ShiftModelPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def firstInput (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let C : Expr (Fin 13) := .var 2
  let X : Expr (Fin 13) := .var 6
  let Y : Expr (Fin 13) := .var 7
  let r : Expr (Fin 13) := .var 8
  let k := .var 9+.var 10
  let b := J*.constant (p 0)
  let q := 1+b
  let q3 := q*(q*q)
  let M := q3*b
  let ell := (X*Y)*(Y*k)
  let A := X+.constant (p 1)*q
  let B := C*A-F*q
  M*((ell+k+r)-k*B)+Y*b-B*q3

/-- A compact signed representation of the actual first-root expression. -/
theorem first_input_rep (p : Fin 4 → ℕ) (v : Fin 13 → V) :
    let b : V := v 0*(p 0:V)
    let q := 1+b
    let q3 := q*(q*q)
    let M := q3*b
    let k := v 9+v 10
    let ell := (v 6*v 7)*(v 7*k)
    let A := v 6+(p 1:V)*q
    SignedRep (firstInput (fun j => (p j:ℤ))) v
      (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let q3 : V := q*(q*q)
  let M : V := q3*b
  let k : V := v 9+v 10
  let ell : V := (v 6*v 7)*(v 7*k)
  let A : V := v 6+(p 1:V)*q
  let eB : Expr (Fin 13) := .var 0*.constant (p 0)
  let eQ : Expr (Fin 13) := 1+eB
  let eQ3 : Expr (Fin 13) := eQ*(eQ*eQ)
  let eM : Expr (Fin 13) := eQ3*eB
  let eK : Expr (Fin 13) := .var 9+.var 10
  let eEll : Expr (Fin 13) := (.var 6*.var 7)*(.var 7*eK)
  let eA : Expr (Fin 13) := .var 6+.constant (p 1)*eQ
  let eBt : Expr (Fin 13) := .var 2*eA-.var 1*eQ
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hQ3 : SignedRep eQ3 v (natural q3) := rep_mul_nat hQ (rep_mul_nat hQ hQ)
  have hM : SignedRep eM v (natural M) := rep_mul_nat hQ3 hB
  have hK : SignedRep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hEll : SignedRep eEll v (natural ell) := rep_mul_nat (rep_mul_nat (rep_var v 6) (rep_var v 7)) (rep_mul_nat (rep_var v 7) hK)
  have hA : SignedRep eA v (natural A) := rep_add_nat (rep_var v 6) (rep_mul_nat (rep_nat v (p 1)) hQ)
  have hBt : SignedRep eBt v (v 2*A,v 1*q) := by
    have ht := rep_sub (rep_mul_nat (rep_var v 2) hA) (rep_mul_nat (rep_var v 1) hQ)
    change SignedRep eBt v (minus (natural (v 2*A)) (natural (v 1*q))) at ht
    simpa only [minus,natural,add_zero,zero_add] using ht
  have hEkR := rep_add_nat (rep_add_nat hEll hK) (rep_var v 8)
  have ht := rep_sub (rep_add (rep_mul hM (rep_sub hEkR (rep_mul hK hBt)))
    (rep_mul_nat (rep_var v 7) hB)) (rep_mul hBt hQ3)
  change SignedRep (firstInput (fun j => (p j:ℤ))) v
    (minus (plus (multiply (natural M) (minus (natural (ell+k+v 8))
      (multiply (natural k) (v 2*A,v 1*q)))) (natural (v 7*b)))
      (multiply (v 2*A,v 1*q) (natural q3))) at ht
  apply equivalent_trans ht
  dsimp [minus,plus,multiply,natural,Equivalent]
  ring
/-- The actual first-root input is invariant under the C/r coordinate shift. -/
theorem first_input_preserved (p : Fin 4 → ℕ) (v w : Fin 13 → V)
    (hJ : w 0=v 0) (hF : w 1=v 1) (hX : w 6=v 6) (hY : w 7=v 7)
    (heta : w 9=v 9) (hzeta : w 10=v 10)
    (hC : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let c := v 9+v 7*(v 9+v 10); w 2=v 2+b*c*U)
    (hr : let b := v 0*(p 0:V); let q := 1+b; let U := v 7*(q*q);
      let k := v 9+v 10; let c := v 9+v 7*k; let A := v 6+(p 1:V)*q;
      w 8=v 8+b*c*U*A*k+c*U*A) :
    Equivalent (pairEval (firstInput (fun j => (p j:ℤ))) w)
      (pairEval (firstInput (fun j => (p j:ℤ))) v) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let q3 : V := q*(q*q)
  let M : V := q3*b
  let U : V := v 7*(q*q)
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let ell : V := (v 6*v 7)*(v 7*k)
  let A : V := v 6+(p 1:V)*q
  have hv := first_input_rep p v
  have hw := first_input_rep p w
  change SignedRep (firstInput (fun j => (p j:ℤ))) v
    (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) at hv
  have hw' : SignedRep (firstInput (fun j => (p j:ℤ))) w
    (M*(ell+k+(v 8+b*c*U*A*k+c*U*A))+v 7*b+(M*k+q3)*(v 1*q),
      (M*k+q3)*((v 2+b*c*U)*A)) := by
    simpa only [hJ,hF,hX,hY,heta,hzeta,hC,hr,b,q,q3,M,U,k,c,ell,A] using hw
  have hc := first_root b q3 c U A k (v 1) q (v 2) (v 8) ell (v 7)
  change Equivalent (M*(ell+k+(v 8+b*c*U*A*k+c*U*A))+v 7*b+(M*k+q3)*(v 1*q),
      (M*k+q3)*((v 2+b*c*U)*A))
    (M*(ell+k+v 8)+v 7*b+(M*k+q3)*(v 1*q),(M*k+q3)*(v 2*A)) at hc
  exact equivalent_trans hw' (equivalent_trans hc (equivalent_symm hv))
end DiophantineConsistency.AdaptiveGap85ShiftFirstInput
