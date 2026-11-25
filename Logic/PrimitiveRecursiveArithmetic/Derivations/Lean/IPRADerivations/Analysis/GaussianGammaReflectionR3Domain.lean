import IPRADerivations.Analysis.GaussianGammaReflectionProduct
import IPRADerivations.Analysis.GaussianSineProductReflectionLower

/-!
# The R3 sine margin on the original complementary Gamma domain

The complementary source supplies the two pole guards through 2R.
Beyond that cutoff, the real coordinate gives the extra guard used
by the sine-product lower bound. Weakening the positive numerator to
one gives a shared source for the explicit sine reciprocal.
-/

set_option autoImplicit false
set_option maxHeartbeats 215000

namespace LeanProofs.IPRA.Analysis.GaussianGammaReflectionR3Domain

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded bounded_neg)
open GaussianGammaEulerHeadLower (poleAt poleGuard pole_at subst_poleGuard)
open GaussianGammaReflectionProduct (complementarySource)
open GaussianSineProductReflectionLower (guardCutoff automatic_pole_at)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem guard_from_old (z R B a d : PTm n)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) (ha : Γ ⊢[PRAAx] le one a) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] poleGuard z B a d (two*R)) :
    Γ ⊢[PRAAx] poleGuard z B one d (guardCutoff R) := by
  refine .allI (.impI ?_)
  let i : PTm (n+1) := var 0
  let sh (t : PTm n) := Syn.shift t
  let Δ := le i (sh (guardCutoff R)) :: Γ.map Fm.shift
  have hb : Δ ⊢[PRAAx] bounded (sh z) (sh R*sh B) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hz.shift.wk
  have ha' : Δ ⊢[PRAAx] le one (sh a) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,one] using ha.shift.wk
  have hd' : Δ ⊢[PRAAx] le one (sh d) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,one] using hd.shift.wk
  have hp : Δ ⊢[PRAAx] poleGuard (sh z) (sh B) (sh a) (sh d) (two*sh R) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,two,one] using h.shift.wk
  have safe : Δ ⊢[PRAAx] le (succ (sh R)) (succ (two*sh R)) :=
    le_of_eq_add (d := sh R) (by ipra_ring)
  have result : Δ ⊢[PRAAx] poleAt (sh z) (sh B) one (sh d) i := by
    refine .orE (lt_or_le (two*sh R) i) ?_ ?_
    · exact automatic_pole_at (sh z) (sh R) (sh B) one (sh d) i hb.wk hd'.wk (le_trans safe.wk Prf.hyp0)
    · have e : le i (two*sh R) :: Δ ⊢[PRAAx] le (one*sh B) (sh a*sh B) :=
        le_mul_mono ha'.wk (le_refl (sh B))
      exact le_trans (le_mul_mono e e) (pole_at (sh z) (sh B) (sh a) (sh d) (two*sh R) i hp.wk Prf.hyp0)
  simpa only [i,sh,Δ,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using result

theorem r3_source (z R B a d e f : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f) :
    Γ ⊢[PRAAx] GaussianSineProductReflectionLower.source z R B one d (two*R) := by
  have hp := hs.andE₁
  have hn := hs.andE₂.andE₁
  have hz := hp.andE₁.andE₂.andE₂
  have ha := hp.andE₂.andE₁
  have hd := hp.andE₂.andE₂.andE₁
  have hpos := guard_from_old z R B a d hz ha hd hp.andE₂.andE₂.andE₂
  have hneg := guard_from_old (ComplexLogarithmRemainder.neg z) R B a d (bounded_neg hz) ha hd hn.andE₂.andE₂.andE₂
  exact .andI (.andI (.andI hp.andE₁.andE₁ hp.andE₁.andE₂.andE₁) (.andI (le_refl one) hd))
    (.andI hz (.andI (le_refl (two*R)) (.andI hpos hneg)))

theorem actual_reflection_R3_domain_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        GaussianSineProductReflectionLower.source (var 0) (var 1) (var 2) one (var 4) (two*var 1)) :=
  closeUniv 7 (.impI (r3_source _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaReflectionR3Domain
