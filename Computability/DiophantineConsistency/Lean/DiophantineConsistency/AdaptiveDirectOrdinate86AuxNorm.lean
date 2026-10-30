import DiophantineConsistency.ArithmeticSignedPairExpressions
import DiophantineConsistency.AdaptiveDirectOrdinate86Units

/-! Auxiliary norm directly from actual direct-ordinate factor units. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Factors AdaptiveDirectOrdinate86Units
open ArithmeticSignedPairExpressions
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) (.add (.var 9) (.var 10)))
def eI : Expr (Fin 13) := .mul (.mul eC eC) (.var 4)
def eQ : Expr (Fin 13) :=
  let a : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  .mul (.add (.add (.constant 3) (.mul (.constant 4) a)) (.mul a a))
    (.sub (.mul (.var 3) (.var 3)) (.constant 1))
def eV (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let b : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let q : Expr (Fin 13) := .add (.constant 1) b
  let rank : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub q (.var 1)) b)) (.sub (.mul q q) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) q)))
  .sub (.mul (.mul (.var 3) (.var 3)) (.sub (.mul (.var 5) eC) rank)) eC

def AuxNorm86 (p : Fin 4 → ℤ) (v : Fin 13 → V) : Prop :=
  let c := v 9+v 7*(v 9+v 10)
  let I := (c*c)*v 4
  let z := magnitude (pairEval (eV p) v)
  let y := v 11
  I*I*z*z+y*y=1+I*I*y*y

/-- The two actual units force the direct-ordinate auxiliary norm, with no
    rank orientation, residue, or positivity premises. -/
theorem expressionAt_aux_norm86 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 p) v) : AuxNorm86 p v := by
  let c : V := v 9+v 7*(v 9+v 10)
  let I : V := (c*c)*v 4
  let z : V := magnitude (pairEval (eV p) v)
  let y : V := v 11
  have hi : SignedRep eI v (natural I) := by
    have hc : SignedRep eC v (natural c) := rep_add_nat (rep_var v 9)
      (rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)))
    exact rep_mul_nat (rep_mul_nat hc hc) (rep_var v 4)
  have hu := (expressionAt_factor_units86 p v hz).2.2.2
  change (pairEval (.add (.constant 1) (.sub (.mul eI eI) eQ)) v).1 =
    (pairEval (.add (.constant 1) (.sub (.mul eI eI) eQ)) v).2+1 at hu
  have hs : SignedRep (.add (.constant 1) (.sub (.mul eI eI) eQ)) v
      (1+I*I+(pairEval eQ v).2,(pairEval eQ v).1) := by
    have h := rep_add (rep_one v) (rep_sub (rep_mul_nat hi hi)
      (equivalent_refl (pairEval eQ v)))
    simpa only [plus,minus,natural,add_zero,zero_add,add_assoc] using h
  have he := represented_unit hu hs
  have hqe : (pairEval eQ v).1=(pairEval eQ v).2+I*I := by
    have ht : 1+((pairEval eQ v).2+I*I)=1+(pairEval eQ v).1 := by
      calc
        _=1+I*I+(pairEval eQ v).2 := by ring
        _=(pairEval eQ v).1+1 := he
        _=1+(pairEval eQ v).1 := by ring
    exact (add_left_cancel ht).symm
  have hq : SignedRep eQ v (natural (I*I)) := by
    change (pairEval eQ v).1+0=(pairEval eQ v).2+I*I
    simpa using hqe
  have hv2 : SignedRep (.mul (eV p) (eV p)) v (natural (z*z)) :=
    equivalent_trans (rep_mul (equivalent_refl _) (equivalent_refl _))
      (square_magnitude (pairEval (eV p) v))
  have hy2 : SignedRep (.mul (.var 11) (.var 11)) v (natural (y*y)) :=
    rep_mul_nat (rep_var v 11) (rep_var v 11)
  have haux : SignedRep (.sub (.mul (.var 11) (.var 11))
      (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v
      (y*y+(I*I)*(z*z),(I*I)*(y*y)) := by
    have h := rep_sub hy2 (rep_mul hq (rep_sub hy2 hv2))
    simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hunit := (expressionAt_factor_units86 p v hz).2.2.1
  change (pairEval (.sub (.mul (.var 11) (.var 11))
    (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v).1 =
    (pairEval (.sub (.mul (.var 11) (.var 11))
    (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v).2+1 at hunit
  have hh := represented_unit hunit haux
  change I*I*z*z+y*y=1+I*I*y*y
  calc
    _=y*y+(I*I)*(z*z) := by ring
    _=(I*I)*(y*y)+1 := hh
    _=1+I*I*y*y := by ring
end DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
