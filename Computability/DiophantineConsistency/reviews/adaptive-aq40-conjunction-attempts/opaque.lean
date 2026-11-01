import DiophantineConsistency.AQ40ContextProbe
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AQ40ZerosProbeV2
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
    fin_cases i
    · change (pairEval r0 v).1 = (pairEval r0 v).2
      tauto
    · change (pairEval r1 v).1 = (pairEval r1 v).2
      tauto
    · change (pairEval r2 v).1 = (pairEval r2 v).2
      tauto
    · change (pairEval r3 v).1 = (pairEval r3 v).2
      tauto
    · change (pairEval r4 v).1 = (pairEval r4 v).2
      tauto
    · change (pairEval r5 v).1 = (pairEval r5 v).2
      tauto
    · change (pairEval r6 v).1 = (pairEval r6 v).2
      tauto
    · change (pairEval r7 v).1 = (pairEval r7 v).2
      tauto
    · change (pairEval r8 v).1 = (pairEval r8 v).2
      tauto
    · change (pairEval r9 v).1 = (pairEval r9 v).2
      tauto
    · change (pairEval r10 v).1 = (pairEval r10 v).2
      tauto
    · change (pairEval r11 v).1 = (pairEval r11 v).2
      tauto
    · change (pairEval r12 v).1 = (pairEval r12 v).2
      tauto
    · change (pairEval r13 v).1 = (pairEval r13 v).2
      tauto
    · change (pairEval r14 v).1 = (pairEval r14 v).2
      tauto
    · change (pairEval r15 v).1 = (pairEval r15 v).2
      tauto
    · change (pairEval r16 v).1 = (pairEval r16 v).2
      tauto
    · change (pairEval r17 v).1 = (pairEval r17 v).2
      tauto
    · change (pairEval r18 v).1 = (pairEval r18 v).2
      tauto
    · change (pairEval r19 v).1 = (pairEval r19 v).2
      tauto
    · change (pairEval r20 v).1 = (pairEval r20 v).2
      tauto
    · change (pairEval r21 v).1 = (pairEval r21 v).2
      tauto
    · change (pairEval r22 v).1 = (pairEval r22 v).2
      tauto
    · change (pairEval r23 v).1 = (pairEval r23 v).2
      tauto
    · change (pairEval r24 v).1 = (pairEval r24 v).2
      tauto
    · change (pairEval r25 v).1 = (pairEval r25 v).2
      tauto
    · change (pairEval r26 v).1 = (pairEval r26 v).2
      tauto
    · change (pairEval r27 v).1 = (pairEval r27 v).2
      tauto
  · intro hh
    have h0 : InternalZero r0 v := hh 0
    change (pairEval r0 v).1 = (pairEval r0 v).2 at h0
    have h1 : InternalZero r1 v := hh 1
    change (pairEval r1 v).1 = (pairEval r1 v).2 at h1
    have h2 : InternalZero r2 v := hh 2
    change (pairEval r2 v).1 = (pairEval r2 v).2 at h2
    have h3 : InternalZero r3 v := hh 3
    change (pairEval r3 v).1 = (pairEval r3 v).2 at h3
    have h4 : InternalZero r4 v := hh 4
    change (pairEval r4 v).1 = (pairEval r4 v).2 at h4
    have h5 : InternalZero r5 v := hh 5
    change (pairEval r5 v).1 = (pairEval r5 v).2 at h5
    have h6 : InternalZero r6 v := hh 6
    change (pairEval r6 v).1 = (pairEval r6 v).2 at h6
    have h7 : InternalZero r7 v := hh 7
    change (pairEval r7 v).1 = (pairEval r7 v).2 at h7
    have h8 : InternalZero r8 v := hh 8
    change (pairEval r8 v).1 = (pairEval r8 v).2 at h8
    have h9 : InternalZero r9 v := hh 9
    change (pairEval r9 v).1 = (pairEval r9 v).2 at h9
    have h10 : InternalZero r10 v := hh 10
    change (pairEval r10 v).1 = (pairEval r10 v).2 at h10
    have h11 : InternalZero r11 v := hh 11
    change (pairEval r11 v).1 = (pairEval r11 v).2 at h11
    have h12 : InternalZero r12 v := hh 12
    change (pairEval r12 v).1 = (pairEval r12 v).2 at h12
    have h13 : InternalZero r13 v := hh 13
    change (pairEval r13 v).1 = (pairEval r13 v).2 at h13
    have h14 : InternalZero r14 v := hh 14
    change (pairEval r14 v).1 = (pairEval r14 v).2 at h14
    have h15 : InternalZero r15 v := hh 15
    change (pairEval r15 v).1 = (pairEval r15 v).2 at h15
    have h16 : InternalZero r16 v := hh 16
    change (pairEval r16 v).1 = (pairEval r16 v).2 at h16
    have h17 : InternalZero r17 v := hh 17
    change (pairEval r17 v).1 = (pairEval r17 v).2 at h17
    have h18 : InternalZero r18 v := hh 18
    change (pairEval r18 v).1 = (pairEval r18 v).2 at h18
    have h19 : InternalZero r19 v := hh 19
    change (pairEval r19 v).1 = (pairEval r19 v).2 at h19
    have h20 : InternalZero r20 v := hh 20
    change (pairEval r20 v).1 = (pairEval r20 v).2 at h20
    have h21 : InternalZero r21 v := hh 21
    change (pairEval r21 v).1 = (pairEval r21 v).2 at h21
    have h22 : InternalZero r22 v := hh 22
    change (pairEval r22 v).1 = (pairEval r22 v).2 at h22
    have h23 : InternalZero r23 v := hh 23
    change (pairEval r23 v).1 = (pairEval r23 v).2 at h23
    have h24 : InternalZero r24 v := hh 24
    change (pairEval r24 v).1 = (pairEval r24 v).2 at h24
    have h25 : InternalZero r25 v := hh 25
    change (pairEval r25 v).1 = (pairEval r25 v).2 at h25
    have h26 : InternalZero r26 v := hh 26
    change (pairEval r26 v).1 = (pairEval r26 v).2 at h26
    have h27 : InternalZero r27 v := hh 27
    change (pairEval r27 v).1 = (pairEval r27 v).2 at h27
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
    fin_cases i
    · change (pairEval r0 v).1 = (pairEval r0 v).2
      tauto
    · change (pairEval r1 v).1 = (pairEval r1 v).2
      tauto
    · change (pairEval r2 v).1 = (pairEval r2 v).2
      tauto
    · change (pairEval r3 v).1 = (pairEval r3 v).2
      tauto
    · change (pairEval r4 v).1 = (pairEval r4 v).2
      tauto
    · change (pairEval r5 v).1 = (pairEval r5 v).2
      tauto
    · change (pairEval r6 v).1 = (pairEval r6 v).2
      tauto
    · change (pairEval r7 v).1 = (pairEval r7 v).2
      tauto
    · change (pairEval r8 v).1 = (pairEval r8 v).2
      tauto
    · exact False.elim (hi rfl)
    · change (pairEval r10 v).1 = (pairEval r10 v).2
      tauto
    · change (pairEval r11 v).1 = (pairEval r11 v).2
      tauto
    · change (pairEval r12 v).1 = (pairEval r12 v).2
      tauto
    · change (pairEval r13 v).1 = (pairEval r13 v).2
      tauto
    · change (pairEval r14 v).1 = (pairEval r14 v).2
      tauto
    · change (pairEval r15 v).1 = (pairEval r15 v).2
      tauto
    · change (pairEval r16 v).1 = (pairEval r16 v).2
      tauto
    · change (pairEval r17 v).1 = (pairEval r17 v).2
      tauto
    · change (pairEval r18 v).1 = (pairEval r18 v).2
      tauto
    · change (pairEval r19 v).1 = (pairEval r19 v).2
      tauto
    · change (pairEval r20 v).1 = (pairEval r20 v).2
      tauto
    · change (pairEval r21 v).1 = (pairEval r21 v).2
      tauto
    · change (pairEval r22 v).1 = (pairEval r22 v).2
      tauto
    · change (pairEval r23 v).1 = (pairEval r23 v).2
      tauto
    · change (pairEval r24 v).1 = (pairEval r24 v).2
      tauto
    · change (pairEval r25 v).1 = (pairEval r25 v).2
      tauto
    · change (pairEval r26 v).1 = (pairEval r26 v).2
      tauto
    · change (pairEval r27 v).1 = (pairEval r27 v).2
      tauto
  · intro hh
    have h0 : InternalZero r0 v := hh 0 (by decide)
    change (pairEval r0 v).1 = (pairEval r0 v).2 at h0
    have h1 : InternalZero r1 v := hh 1 (by decide)
    change (pairEval r1 v).1 = (pairEval r1 v).2 at h1
    have h2 : InternalZero r2 v := hh 2 (by decide)
    change (pairEval r2 v).1 = (pairEval r2 v).2 at h2
    have h3 : InternalZero r3 v := hh 3 (by decide)
    change (pairEval r3 v).1 = (pairEval r3 v).2 at h3
    have h4 : InternalZero r4 v := hh 4 (by decide)
    change (pairEval r4 v).1 = (pairEval r4 v).2 at h4
    have h5 : InternalZero r5 v := hh 5 (by decide)
    change (pairEval r5 v).1 = (pairEval r5 v).2 at h5
    have h6 : InternalZero r6 v := hh 6 (by decide)
    change (pairEval r6 v).1 = (pairEval r6 v).2 at h6
    have h7 : InternalZero r7 v := hh 7 (by decide)
    change (pairEval r7 v).1 = (pairEval r7 v).2 at h7
    have h8 : InternalZero r8 v := hh 8 (by decide)
    change (pairEval r8 v).1 = (pairEval r8 v).2 at h8
    have h10 : InternalZero r10 v := hh 10 (by decide)
    change (pairEval r10 v).1 = (pairEval r10 v).2 at h10
    have h11 : InternalZero r11 v := hh 11 (by decide)
    change (pairEval r11 v).1 = (pairEval r11 v).2 at h11
    have h12 : InternalZero r12 v := hh 12 (by decide)
    change (pairEval r12 v).1 = (pairEval r12 v).2 at h12
    have h13 : InternalZero r13 v := hh 13 (by decide)
    change (pairEval r13 v).1 = (pairEval r13 v).2 at h13
    have h14 : InternalZero r14 v := hh 14 (by decide)
    change (pairEval r14 v).1 = (pairEval r14 v).2 at h14
    have h15 : InternalZero r15 v := hh 15 (by decide)
    change (pairEval r15 v).1 = (pairEval r15 v).2 at h15
    have h16 : InternalZero r16 v := hh 16 (by decide)
    change (pairEval r16 v).1 = (pairEval r16 v).2 at h16
    have h17 : InternalZero r17 v := hh 17 (by decide)
    change (pairEval r17 v).1 = (pairEval r17 v).2 at h17
    have h18 : InternalZero r18 v := hh 18 (by decide)
    change (pairEval r18 v).1 = (pairEval r18 v).2 at h18
    have h19 : InternalZero r19 v := hh 19 (by decide)
    change (pairEval r19 v).1 = (pairEval r19 v).2 at h19
    have h20 : InternalZero r20 v := hh 20 (by decide)
    change (pairEval r20 v).1 = (pairEval r20 v).2 at h20
    have h21 : InternalZero r21 v := hh 21 (by decide)
    change (pairEval r21 v).1 = (pairEval r21 v).2 at h21
    have h22 : InternalZero r22 v := hh 22 (by decide)
    change (pairEval r22 v).1 = (pairEval r22 v).2 at h22
    have h23 : InternalZero r23 v := hh 23 (by decide)
    change (pairEval r23 v).1 = (pairEval r23 v).2 at h23
    have h24 : InternalZero r24 v := hh 24 (by decide)
    change (pairEval r24 v).1 = (pairEval r24 v).2 at h24
    have h25 : InternalZero r25 v := hh 25 (by decide)
    change (pairEval r25 v).1 = (pairEval r25 v).2 at h25
    have h26 : InternalZero r26 v := hh 26 (by decide)
    change (pairEval r26 v).1 = (pairEval r26 v).2 at h26
    have h27 : InternalZero r27 v := hh 27 (by decide)
    change (pairEval r27 v).1 = (pairEval r27 v).2 at h27
    tauto
#print axioms zero_oldSum
#print axioms zero_newSum
end DiophantineConsistency.AQ40ZerosProbeV2
