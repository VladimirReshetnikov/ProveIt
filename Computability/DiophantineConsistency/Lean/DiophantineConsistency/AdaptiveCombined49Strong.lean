import DiophantineConsistency.AdaptiveNamedValues50
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.AdaptiveCombined49Strong
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveNamedValues50 AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011 AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem strong_zero (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (hz : InternalZero (literal p) v) :
    InternalZero ((residualsAt p 3).subst (fill holes)) v := by
  have hc := ((literal_zero_parts p v).mp hz).1
  let r0 := (residualsAt p 0).subst (fill holes)
  let r1 := (residualsAt p 1).subst (fill holes)
  let r2 := (residualsAt p 2).subst (fill holes)
  let r3 := (residualsAt p 3).subst (fill holes)
  let r4 := (residualsAt p 4).subst (fill holes)
  let r5 := (residualsAt p 5).subst (fill holes)
  let r6 := (residualsAt p 6).subst (fill holes)
  let r7 := (residualsAt p 7).subst (fill holes)
  let r8 := (residualsAt p 8).subst (fill holes)
  let r9 := (residualsAt p 9).subst (fill holes)
  let r10 := (residualsAt p 10).subst (fill holes)
  let r11 := (residualsAt p 11).subst (fill holes)
  let r12 := (residualsAt p 12).subst (fill holes)
  let r13 := (residualsAt p 13).subst (fill holes)
  let r14 := (residualsAt p 14).subst (fill holes)
  let r15 := (residualsAt p 15).subst (fill holes)
  let r16 := (residualsAt p 16).subst (fill holes)
  let r17 := (residualsAt p 17).subst (fill holes)
  let r18 := (residualsAt p 18).subst (fill holes)
  let r19 := (residualsAt p 19).subst (fill holes)
  let r20 := (residualsAt p 20).subst (fill holes)
  let r21 := (residualsAt p 21).subst (fill holes)
  let r22 := (residualsAt p 22).subst (fill holes)
  let r23 := (residualsAt p 23).subst (fill holes)
  let r24 := (residualsAt p 24).subst (fill holes)
  let r25 := (residualsAt p 25).subst (fill holes)
  let r26 := (residualsAt p 26).subst (fill holes)
  let r27 := (residualsAt p 27).subst (fill holes)
  let base := r0*r0+r1*r1+r2*r2+r3*r3+r4*r4+r5*r5+r6*r6+r7*r7+r8*r8+r9*r9+r10*r10+r11*r11+r12*r12+r13*r13+r14*r14+r15*r15+r16*r16+r17*r17+r18*r18+r19*r19+r20*r20+r21*r21+r22*r22+r23*r23+r24*r24+r25*r25+r26*r26+r27*r27
  have hrep := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (AdaptiveSquareWitnessDirect14.rawSquare_rep r0 v) (AdaptiveSquareWitnessDirect14.rawSquare_rep r1 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r2 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r3 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r4 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r5 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r6 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r7 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r8 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r9 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r10 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r11 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r12 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r13 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r14 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r15 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r16 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r17 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r18 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r19 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r20 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r21 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r22 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r23 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r24 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r25 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r26 v)) (AdaptiveSquareWitnessDirect14.rawSquare_rep r27 v)
  change SignedRep base v (natural _) at hrep
  change InternalZero base v at hc
  have hh := (rep_zero_iff hrep).mp hc
  simp only [sum_eq_zero_iff, mul_self_eq_zero, magnitude_zero_iff] at hh
  change (pairEval r3 v).1 = (pairEval r3 v).2
  tauto
theorem strong_relation (p : Fin 4 → ℤ) (v : Fin 50 → V)
    (hz : InternalZero (literal p) v) :
    v 38 * v 38 + v 41 = v 40 := by
  have hs := strong_zero p v hz
  change InternalZero ((.var 38 * .var 38) - (.var 40 - .var 41) : Expr (Fin 50)) v at hs
  simp only [InternalZero, HSub.hSub, Sub.sub, HMul.hMul, Mul.mul,
    Expr.splitNatural, NatExpr.evalSemiring] at hs
  change v 38 * v 38 + (0 : V) * 0 + (0 + v 41) =
    v 38 * 0 + 0 * v 38 + (v 40 + 0) at hs
  simpa only [mul_zero, zero_mul, add_zero, zero_add] using hs
end DiophantineConsistency.AdaptiveCombined49Strong
