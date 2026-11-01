import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
import DiophantineConsistency.AdaptiveDirectOrdinate86Transport

/-! Signed V represented by the actual nonnegative rank when transport is positive. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86SignedV
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86AuxNorm
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem signedV_rep (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hF : v 1≤1+v 0*(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let c : V := v 9+v 7*(v 9+v 10)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    let L : V := (v 3*v 3)*v 5*c
    let M : V := (v 3*v 3)*R+c
    Equivalent (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV (fun j => (p j:ℤ))) v) (L,M) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eF : Expr (Fin 13) := .var 3
  let eR : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eV : Expr (Fin 13) := .sub (.mul (.mul eF eF) (.sub (.mul (.var 5) eC) eR)) eC
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let L : V := (v 3*v 3)*v 5*c
  let M : V := (v 3*v 3)*R+c
  have hq : 1≤q := by dsimp [q]; simp
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R'=R := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  have hB : SignedRep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : SignedRep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hK : SignedRep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hC : SignedRep eC v (natural c) := rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) hK)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR' : SignedRep eR v (natural R') := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hR : SignedRep eR v (natural R) := by rw [hRank] at hR'; exact hR'
  have hF2 : SignedRep (.mul eF eF) v (natural (v 3*v 3)) := rep_mul_nat (rep_var v 3) (rep_var v 3)
  have hV : SignedRep eV v (L,M) := by
    have h := rep_sub (rep_mul hF2 (rep_sub (rep_mul_nat (rep_var v 5) hC) hR)) hC
    simpa only [L,M,multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul,mul_assoc] using h
  exact hV
end DiophantineConsistency.AdaptiveDirectOrdinate86SignedV
