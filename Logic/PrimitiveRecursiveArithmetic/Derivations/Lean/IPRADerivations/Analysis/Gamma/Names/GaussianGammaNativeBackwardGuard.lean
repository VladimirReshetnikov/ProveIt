import IPRADerivations.Analysis.Gamma.GaussianGammaHalfPlaneInputContinuity

/-!
# Pole guard for a backward native Gamma shift

The original positive margin at z supplies all pole factors after the
zeroth factor at z−1. The supplied lower bound for that factor completes
the original guard on the enlarged disk.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNativeBackwardGuard

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (bounded bounded_add bounded_neg bounded_scale normSq normSq_one oneCode scale)
open GaussianGammaEulerHeadLower (poleAt poleGuard translated translated_zero)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaRightHalfPlane (realMargin real_margin_pole_at)
open GaussianNameReciprocal (lower)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRootAlgebra (equal equal_of_values equal_of_code equal_trans normSq_equal sub)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def back (z B : PTm n) : PTm n := sub z (scale B oneCode)

@[simp] theorem subst_back {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (back z B) = back (Syn.subst σ z) (Syn.subst σ B) := by simp [back]

theorem translated_back_succ (z B k : PTm n) :
    Γ ⊢[PRAAx] equal (translated (back z B) B (succ k)) (translated z B k) := by
  apply equal_of_values <;>
    simp only [back,translated,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem shifted_back (z B : PTm n) : Γ ⊢[PRAAx] equal (shifted (back z B) B) z :=
  equal_trans (translated_back_succ z B zero) (translated_zero z B)

private theorem pole_index_congr (w B D : PTm n) {j k : PTm n} (h : Γ ⊢[PRAAx] j ≐ k)
    (hp : Γ ⊢[PRAAx] poleAt w B one D j) : Γ ⊢[PRAAx] poleAt w B one D k := by
  have e : Γ ⊢[PRAAx] translated w B j ≐ translated w B k := by
    simpa only [GaussianGammaEulerHeadLower.subst_translated,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (translated (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![w,B,j]) (σ' := ![w,B,k])
        (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact h)
  exact le_congr (.eqRefl _) (congrMul (.eqRefl (D*D)) (normSq_equal (equal_of_code e))) hp

private theorem weaken_pole_denominator (w B d D k : PTm n) (h : Γ ⊢[PRAAx] le d D)
    (hp : Γ ⊢[PRAAx] poleAt w B one d k) : Γ ⊢[PRAAx] poleAt w B one D k :=
  le_trans hp (mul_le_mul_right (normSq (translated w B k)) (le_mul_mono h h))

private theorem back_pole_at (z B A H k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hH : Γ ⊢[PRAAx] le one H) (hm : Γ ⊢[PRAAx] realMargin z B A)
    (hLower : Γ ⊢[PRAAx] lower (ofGaussian (back z B) B) H) :
    Γ ⊢[PRAAx] poleAt (back z B) B one (A*H) k := by
  let w := back z B
  have lower := GaussianRationalLowerBounds.lower_to_cleared (ofGaussian w B) w B one H hB hH
    (ofGaussian_represents w B hB) hLower
  have hz : Γ ⊢[PRAAx] poleAt w B one H zero :=
    le_congr (by ipra_ring) (congrMul (.eqRefl (H*H)) (normSq_equal (translated_zero (Γ := Γ) w B)).eqSymm) lower
  have weakerH : Γ ⊢[PRAAx] le H (A*H) :=
    le_congr (one_mul H) (.eqRefl _) (mul_le_mul_right H hA)
  have weakerA : Γ ⊢[PRAAx] le A (A*H) :=
    le_congr (one_mul A) (mul_comm H A) (mul_le_mul_right A hH)
  refine .orE (zero_or_succ k) ?_ ?_
  · exact pole_index_congr w B (A*H) Prf.hyp0.eqSymm
      (weaken_pole_denominator w B H (A*H) zero weakerH hz).wk
  · have hm' : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] realMargin z B A := hm.wk
    have step := real_margin_pole_at z B A (pred k) hm'
    have norm := normSq_equal (translated_back_succ (Γ := (k ≐ succ (pred k)) :: Γ) z B (pred k))
    have backStep : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] poleAt w B one A (succ (pred k)) :=
      le_congr (.eqRefl _) (congrMul (.eqRefl (A*A)) norm.eqSymm) step
    exact pole_index_congr w B (A*H) Prf.hyp0.eqSymm
      (weaken_pole_denominator w B A (A*H) (succ (pred k)) weakerA.wk backStep)

private theorem back_pole_guard (z B A H N : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hH : Γ ⊢[PRAAx] le one H) (hm : Γ ⊢[PRAAx] realMargin z B A)
    (hLower : Γ ⊢[PRAAx] lower (ofGaussian (back z B) B) H) :
    Γ ⊢[PRAAx] poleGuard (back z B) B one (A*H) N := by
  let sh (t : PTm n) := Syn.shift t
  have as : Γ.map Fm.shift ⊢[PRAAx] le one (sh A) := by simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (sh H) := by simpa [Fm.shift,Syn.shift,sh] using hH.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] realMargin (sh z) (sh B) (sh A) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  have ls : Γ.map Fm.shift ⊢[PRAAx] lower (ofGaussian (back (sh z) (sh B)) (sh B)) (sh H) := by
    simpa [Fm.shift,Syn.shift,sh] using hLower.shift
  refine .allI (.impI ?_)
  simpa only [sh,Syn.shift,subst_back,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    (back_pole_at (sh z) (sh B) (sh A) (sh H) (var 0) as bs hs ms ls).wk

theorem backward_source (z R B A H : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianGammaHalfPlaneInputContinuity.source z R B A)
    (hH : Γ ⊢[PRAAx] le one H)
    (hLower : Γ ⊢[PRAAx] lower (ofGaussian (back z B) B) H) :
    Γ ⊢[PRAAx] GaussianGammaReciprocalInverse.source (back z B) (R+one) B one (A*H) := by
  have hA := hz.andE₁.andE₁
  have hB := hz.andE₁.andE₂.andE₁.andE₁
  have pos := le_trans hz.andE₂ (le_add_right R one)
  have unity : Γ ⊢[PRAAx] bounded (oneCode : PTm n) one :=
    le_congr normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have wide : Γ ⊢[PRAAx] bounded (back z B) ((R+one)*B) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (bounded_add hz.andE₁.andE₂.andE₁.andE₂ (bounded_neg (bounded_scale B unity)))
  exact .andI (.andI pos (.andI hB wide)) (.andI (le_refl one) (.andI (positive_product A H hA hH)
    (back_pole_guard z B A H (two*(R+one)) hA hB hH hz.andE₁.andE₂.andE₂ hLower)))

theorem actual_original_Gamma_backward_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((GaussianGammaHalfPlaneInputContinuity.source (var 0) (var 1) (var 2) (var 3) ⋏
      (le one (var 4) ⋏ lower (ofGaussian (back (var 0) (var 2)) (var 2)) (var 4))) ⟶
      (GaussianGammaReciprocalInverse.source (back (var 0) (var 2)) (var 1+one) (var 2) one (var 3*var 4) ⋏
        equal (shifted (back (var 0) (var 2)) (var 2)) (var 0))) :=
  closeUniv 5 (.impI (.andI (backward_source _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (shifted_back _ _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNativeBackwardGuard
