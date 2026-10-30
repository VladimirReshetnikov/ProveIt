import DiophantineConsistency.AdaptiveDirectOrdinate86SignedV
import DiophantineConsistency.AdaptiveDirectOrdinate86Witness
import DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011

/-! Actual positive 87 zero yields a positive-shifted 86 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Reverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveAuxNorm2011 ArithmeticAdaptiveTransport2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Witness
open AdaptiveDirectOrdinate86AuxNorm AdaptiveDirectOrdinate86SignedV
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signedV_eval_old (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    pairEval (eV p) (fun i => v (oldIndex i)) = splitEval (signedV p) v := by
  change splitEval (eV p) (fun i => v (oldIndex i)) = splitEval (signedV p) v
  simp only [eV,signedV,eC,splitEval_add,splitEval_sub,splitEval_mul]
  simp [splitEval,Expr.splitNatural,NatExpr.evalSemiring,oldIndex,embed,
    AdaptiveFirstRootFactor87.pairAdd,AdaptiveFirstRootFactor87.pairSub,
    AdaptiveFirstRootFactor87.pairMul,AdaptiveFirstRootFactor87.pairNeg]

theorem old_positive_zero_to_new_natural86 (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hv : ∀i : Fin 13,0<v (oldIndex i))
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (p j:ℤ)))
      (fun i => v (oldIndex i))) :
    ∃ w : Fin 13 → V, InternalZero (positiveShift (expressionAt86 (fun j => (p j:ℤ)))) w := by
  let u : Fin 13 → V := fun i => v (oldIndex i)
  let q : V := 1+u 0*(p 0:V)
  let k : V := u 9+u 10
  let c : V := u 9+u 7*k
  let I : V := (c*c)*u 4
  let R : V := ((q-1)*(q-u 1)+u 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*u 0
  let L : V := (u 3*u 3)*u 5*c
  let M : V := (u 3*u 3)*R+c
  let z : V := magnitude (L,M)
  have hzero : InternalZero (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u := by
    change (splitEval (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u).1 =
      (splitEval (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u).2
    rw [AdaptiveFirstRootFactor87Literal.split_expression_eq]
    exact hz
  have hg := expressionAt_transport_positive p u hb hv hzero
  have hgap : u 1+u 2<q := tsub_pos_iff_lt.mp hg.2
  have hF : u 1≤q := le_trans (by simp : u 1≤u 1+u 2) (le_of_lt hgap)
  have hrep := signedV_rep p u hF
  rw [show pairEval (eV (fun j => (p j:ℤ))) u = splitEval (signedV (fun j => (p j:ℤ))) v by
    exact signedV_eval_old _ v] at hrep
  have hu : u 11=v 13 := by simp [u,oldIndex]
  have hyrep : Equivalent ((splitEval (signedV (fun j => (p j:ℤ))) v).1+v 13,
      (splitEval (signedV (fun j => (p j:ℤ))) v).2) (L+v 13,M) := by
    change (splitEval (signedV (fun j => (p j:ℤ))) v).1+M =
      (splitEval (signedV (fun j => (p j:ℤ))) v).2+L at hrep
    change ((splitEval (signedV (fun j => (p j:ℤ))) v).1+v 13)+M =
      (splitEval (signedV (fun j => (p j:ℤ))) v).2+(L+v 13)
    calc
      _=((splitEval (signedV (fun j => (p j:ℤ))) v).1+M)+v 13 := by ring
      _=((splitEval (signedV (fun j => (p j:ℤ))) v).2+L)+v 13 := by rw [hrep]
      _=_ := by ring
  have hmag := magnitude_equivalent hyrep
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) hk)
  have hc2 : 2≤c := by
    have h := add_le_add (pos_iff_one_le.mp (hv 9))
      (one_le_mul (pos_iff_one_le.mp (hv 7)) (pos_iff_one_le.mp hk))
    simpa only [one_add_one_eq_two] using h
  have hI : 2≤I := calc
    2≤c := hc2
    _≤c*c := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hc)
    _≤c*c*u 4 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 4))
    _=I := rfl
  have hn := expressionAt_aux_norm p u hb hv hzero
  change I*I*z*z+magnitude (L+u 11,M)*magnitude (L+u 11,M) =
    1+I*I*magnitude (L+u 11,M)*magnitude (L+u 11,M) at hn
  rw [hu,←hmag] at hn
  exact old_positive_zero_to_new_natural_of_aux_norm (fun j => (p j:ℤ)) v I z hv hI hn hz
end DiophantineConsistency.AdaptiveDirectOrdinate86Reverse
