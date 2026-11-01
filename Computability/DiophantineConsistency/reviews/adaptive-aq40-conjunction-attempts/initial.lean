import DiophantineConsistency.AQ40ContextProbe
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AQ40ZerosProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums
open AQ40ContextProbe
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem zero_oldSum {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 39 → Expr σ) (v : σ → V) :
    InternalZero ((oldSum p).subst f) v ↔ ∀ i : Fin 28, InternalZero ((residuals p i).subst f) v := by
  let r0 := (residuals p 0).subst f
  let r1 := (residuals p 1).subst f
  let r2 := (residuals p 2).subst f
  let r3 := (residuals p 3).subst f
  let r4 := (residuals p 4).subst f
  let r5 := (residuals p 5).subst f
  let r6 := (residuals p 6).subst f
  let r7 := (residuals p 7).subst f
  let r8 := (residuals p 8).subst f
  let r9 := (residuals p 9).subst f
  let r10 := (residuals p 10).subst f
  let r11 := (residuals p 11).subst f
  let r12 := (residuals p 12).subst f
  let r13 := (residuals p 13).subst f
  let r14 := (residuals p 14).subst f
  let r15 := (residuals p 15).subst f
  let r16 := (residuals p 16).subst f
  let r17 := (residuals p 17).subst f
  let r18 := (residuals p 18).subst f
  let r19 := (residuals p 19).subst f
  let r20 := (residuals p 20).subst f
  let r21 := (residuals p 21).subst f
  let r22 := (residuals p 22).subst f
  let r23 := (residuals p 23).subst f
  let r24 := (residuals p 24).subst f
  let r25 := (residuals p 25).subst f
  let r26 := (residuals p 26).subst f
  let r27 := (residuals p 27).subst f
  let base := r0*r0+r1*r1+r2*r2+r3*r3+r4*r4+r5*r5+r6*r6+r7*r7+r8*r8+r9*r9+r10*r10+r11*r11+r12*r12+r13*r13+r14*r14+r15*r15+r16*r16+r17*r17+r18*r18+r19*r19+r20*r20+r21*r21+r22*r22+r23*r23+r24*r24+r25*r25+r26*r26+r27*r27
  have hrep := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep r0 v) (rawSquare_rep r1 v)) (rawSquare_rep r2 v)) (rawSquare_rep r3 v)) (rawSquare_rep r4 v)) (rawSquare_rep r5 v)) (rawSquare_rep r6 v)) (rawSquare_rep r7 v)) (rawSquare_rep r8 v)) (rawSquare_rep r9 v)) (rawSquare_rep r10 v)) (rawSquare_rep r11 v)) (rawSquare_rep r12 v)) (rawSquare_rep r13 v)) (rawSquare_rep r14 v)) (rawSquare_rep r15 v)) (rawSquare_rep r16 v)) (rawSquare_rep r17 v)) (rawSquare_rep r18 v)) (rawSquare_rep r19 v)) (rawSquare_rep r20 v)) (rawSquare_rep r21 v)) (rawSquare_rep r22 v)) (rawSquare_rep r23 v)) (rawSquare_rep r24 v)) (rawSquare_rep r25 v)) (rawSquare_rep r26 v)) (rawSquare_rep r27 v)
  change SignedRep base v (natural _) at hrep
  change InternalZero base v ↔ _
  rw [rep_zero_iff hrep]
  simp only [sum_eq_zero_iff, mul_self_eq_zero, magnitude_zero_iff]
  constructor
  · intro hh i
    fin_cases i <;> simp_all [InternalZero, pairEval]
  · intro hh
    have h0 : InternalZero r0 v := hh 0
    have h1 : InternalZero r1 v := hh 1
    have h2 : InternalZero r2 v := hh 2
    have h3 : InternalZero r3 v := hh 3
    have h4 : InternalZero r4 v := hh 4
    have h5 : InternalZero r5 v := hh 5
    have h6 : InternalZero r6 v := hh 6
    have h7 : InternalZero r7 v := hh 7
    have h8 : InternalZero r8 v := hh 8
    have h9 : InternalZero r9 v := hh 9
    have h10 : InternalZero r10 v := hh 10
    have h11 : InternalZero r11 v := hh 11
    have h12 : InternalZero r12 v := hh 12
    have h13 : InternalZero r13 v := hh 13
    have h14 : InternalZero r14 v := hh 14
    have h15 : InternalZero r15 v := hh 15
    have h16 : InternalZero r16 v := hh 16
    have h17 : InternalZero r17 v := hh 17
    have h18 : InternalZero r18 v := hh 18
    have h19 : InternalZero r19 v := hh 19
    have h20 : InternalZero r20 v := hh 20
    have h21 : InternalZero r21 v := hh 21
    have h22 : InternalZero r22 v := hh 22
    have h23 : InternalZero r23 v := hh 23
    have h24 : InternalZero r24 v := hh 24
    have h25 : InternalZero r25 v := hh 25
    have h26 : InternalZero r26 v := hh 26
    have h27 : InternalZero r27 v := hh 27
    simp only [InternalZero, pairEval] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
    tauto
theorem zero_newSum {σ : Type*} (p : Fin 4 → ℤ) (f : Fin 2 ⊕ Fin 39 → Expr σ) (v : σ → V) :
    InternalZero ((newSum p).subst f) v ↔ ∀ i : Fin 28, i ≠ 9 → InternalZero ((residuals p i).subst f) v := by
  let r0 := (residuals p 0).subst f
  let r1 := (residuals p 1).subst f
  let r2 := (residuals p 2).subst f
  let r3 := (residuals p 3).subst f
  let r4 := (residuals p 4).subst f
  let r5 := (residuals p 5).subst f
  let r6 := (residuals p 6).subst f
  let r7 := (residuals p 7).subst f
  let r8 := (residuals p 8).subst f
  let r10 := (residuals p 10).subst f
  let r11 := (residuals p 11).subst f
  let r12 := (residuals p 12).subst f
  let r13 := (residuals p 13).subst f
  let r14 := (residuals p 14).subst f
  let r15 := (residuals p 15).subst f
  let r16 := (residuals p 16).subst f
  let r17 := (residuals p 17).subst f
  let r18 := (residuals p 18).subst f
  let r19 := (residuals p 19).subst f
  let r20 := (residuals p 20).subst f
  let r21 := (residuals p 21).subst f
  let r22 := (residuals p 22).subst f
  let r23 := (residuals p 23).subst f
  let r24 := (residuals p 24).subst f
  let r25 := (residuals p 25).subst f
  let r26 := (residuals p 26).subst f
  let r27 := (residuals p 27).subst f
  let base := r0*r0+r1*r1+r2*r2+r3*r3+r4*r4+r5*r5+r6*r6+r7*r7+r8*r8+r10*r10+r11*r11+r12*r12+r13*r13+r14*r14+r15*r15+r16*r16+r17*r17+r18*r18+r19*r19+r20*r20+r21*r21+r22*r22+r23*r23+r24*r24+r25*r25+r26*r26+r27*r27
  have hrep := rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rep_add_nat (rawSquare_rep r0 v) (rawSquare_rep r1 v)) (rawSquare_rep r2 v)) (rawSquare_rep r3 v)) (rawSquare_rep r4 v)) (rawSquare_rep r5 v)) (rawSquare_rep r6 v)) (rawSquare_rep r7 v)) (rawSquare_rep r8 v)) (rawSquare_rep r10 v)) (rawSquare_rep r11 v)) (rawSquare_rep r12 v)) (rawSquare_rep r13 v)) (rawSquare_rep r14 v)) (rawSquare_rep r15 v)) (rawSquare_rep r16 v)) (rawSquare_rep r17 v)) (rawSquare_rep r18 v)) (rawSquare_rep r19 v)) (rawSquare_rep r20 v)) (rawSquare_rep r21 v)) (rawSquare_rep r22 v)) (rawSquare_rep r23 v)) (rawSquare_rep r24 v)) (rawSquare_rep r25 v)) (rawSquare_rep r26 v)) (rawSquare_rep r27 v)
  change SignedRep base v (natural _) at hrep
  change InternalZero base v ↔ _
  rw [rep_zero_iff hrep]
  simp only [sum_eq_zero_iff, mul_self_eq_zero, magnitude_zero_iff]
  constructor
  · intro hh i
    intro hi
    fin_cases i <;> simp_all [InternalZero, pairEval]
  · intro hh
    have h0 : InternalZero r0 v := hh 0 (by decide)
    have h1 : InternalZero r1 v := hh 1 (by decide)
    have h2 : InternalZero r2 v := hh 2 (by decide)
    have h3 : InternalZero r3 v := hh 3 (by decide)
    have h4 : InternalZero r4 v := hh 4 (by decide)
    have h5 : InternalZero r5 v := hh 5 (by decide)
    have h6 : InternalZero r6 v := hh 6 (by decide)
    have h7 : InternalZero r7 v := hh 7 (by decide)
    have h8 : InternalZero r8 v := hh 8 (by decide)
    have h10 : InternalZero r10 v := hh 10 (by decide)
    have h11 : InternalZero r11 v := hh 11 (by decide)
    have h12 : InternalZero r12 v := hh 12 (by decide)
    have h13 : InternalZero r13 v := hh 13 (by decide)
    have h14 : InternalZero r14 v := hh 14 (by decide)
    have h15 : InternalZero r15 v := hh 15 (by decide)
    have h16 : InternalZero r16 v := hh 16 (by decide)
    have h17 : InternalZero r17 v := hh 17 (by decide)
    have h18 : InternalZero r18 v := hh 18 (by decide)
    have h19 : InternalZero r19 v := hh 19 (by decide)
    have h20 : InternalZero r20 v := hh 20 (by decide)
    have h21 : InternalZero r21 v := hh 21 (by decide)
    have h22 : InternalZero r22 v := hh 22 (by decide)
    have h23 : InternalZero r23 v := hh 23 (by decide)
    have h24 : InternalZero r24 v := hh 24 (by decide)
    have h25 : InternalZero r25 v := hh 25 (by decide)
    have h26 : InternalZero r26 v := hh 26 (by decide)
    have h27 : InternalZero r27 v := hh 27 (by decide)
    simp only [InternalZero, pairEval] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
    tauto
#print axioms zero_oldSum
#print axioms zero_newSum
end DiophantineConsistency.AQ40ZerosProbe
