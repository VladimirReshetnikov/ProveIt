import IPRADerivations.Analysis.GaussianGammaEulerInverseConvergence

/-!
# The positive real-part margin supplies the original Gamma guards

The Euler-integral input satisfies Re(z/B) ≥ 1/A. Its horizontal
displacement from every nonpositive integer therefore supplies the
original pole margin (1,A), uniformly in the factor index and radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRightHalfPlane

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open GaussianGammaEulerHeadLower (translated poleAt poleGuard)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaEulerInverseConvergence (actual_rate coefficientNumerator coefficientDenominator)
open GaussianNamedInverseRate (independentRate)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (re im scale normSq normSq_eval normSq_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def realMargin (z B A : PTm n) : Fm PTm n := zle (ZT.ofNat B) (ZT.ofNat A*re z)
@[simp] theorem subst_realMargin {m : ℕ} (σ : Fin n → PTm m) (z B A : PTm n) :
    (realMargin z B A).subst σ = realMargin (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ A) := by
  have e (u v : ZT n) : (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by simp [zle, ZT.subst]
  simp only [realMargin, e, ZT.subst_mul, ZT.subst_ofNat, ComplexLogarithmRemainder.subst_re]

theorem real_margin_pole_at (z B A k : PTm n) (hm : Γ ⊢[PRAAx] realMargin z B A) :
    Γ ⊢[PRAAx] poleAt z B one A k := by
  let u := ZT.ofNat B
  let v := ZT.ofNat A*re z
  let w := monus (v.pos+u.neg) (u.pos+v.neg)
  let t := scale A (translated z B k)
  let d := w+A*B*k
  have hw : ZT.toZ Γ u+𝔞 w = ZT.toZ Γ v := zle_toZ hm
  have hreal : ZT.toZ Γ (re t) = 𝔞 B+𝔞 d := by
    simp only [t, translated, d, u, v, ZT.toZ_mul, ZT.toZ_ofNat, GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_add, GaussianRootAlgebra.re_one] at hw ⊢
    ipra_simps
    linear_combination -hw
  have hi := sq_nat (Γ := Γ) (im t)
  simp only [ZT.toZ_sq] at hi
  let m := ad (im t).pos (im t).neg
  have hnorm : Γ ⊢[PRAAx] le (B*B) (normSq t) := by
    apply le_of_eq_add (d := B*d+B*d+d*d+m*m)
    apply deriveNat
    ipra_simps
    rw [normSq_eval, hreal, hi]
    unfold m
    ipra_simps
    ring
  exact le_congr (by ipra_ring) (normSq_scale A (translated z B k)) hnorm

theorem real_margin_pole_guard (z B A N : PTm n) (hm : Γ ⊢[PRAAx] realMargin z B A) :
    Γ ⊢[PRAAx] poleGuard z B one A N := by
  refine .allI (.impI ?_)
  have h : Γ.map Fm.shift ⊢[PRAAx] realMargin (Syn.shift z) (Syn.shift B) (Syn.shift A) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  simpa only [poleGuard, Syn.shift, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    real_margin_pole_at (Syn.shift z) (Syn.shift B) (Syn.shift A) (var 0) h.wk

theorem original_right_half_plane_source (z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hA : Γ ⊢[PRAAx] le one A) (hm : Γ ⊢[PRAAx] realMargin z B A) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source z R B one A :=
  .andI h (.andI (le_refl one) (.andI hA (real_margin_pole_guard _ _ _ _ hm)))

theorem original_right_half_plane_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realMargin (var 0) (var 1) (var 2) ⟶ poleGuard (var 0) (var 1) one (var 2) (var 3)) :=
  closeUniv 4 (.impI (real_margin_pole_guard _ _ _ _ Prf.hyp0))

theorem original_right_half_plane_Gamma_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
      realMargin (var 0) (var 2) (var 3) ⟶ pointCN gammaF (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (gamma_regular _ _ _ _ _
    (original_right_half_plane_source _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0)))))

theorem original_right_half_plane_euler_rate (z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B)
    (hA : Γ ⊢[PRAAx] le one A) (hm : Γ ⊢[PRAAx] realMargin z B A)
    (hN : Γ ⊢[PRAAx] le (two*R) N ⋏ le (GaussianGammaPerturbationExponent.numerator R) N) :
    Γ ⊢[PRAAx] independentRate eulerF gammaF (eulerData z R B A N) (gammaData z R B A)
      (coefficientNumerator R A) (coefficientDenominator R one N) :=
  actual_rate z R B one A N (.andI (original_right_half_plane_source z R B A h hA hm) hN)

theorem original_right_half_plane_C15_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ le one (var 3) ⟶
      realMargin (var 0) (var 2) (var 3) ⟶
      (le (two*var 1) (var 4) ⋏ le (GaussianGammaPerturbationExponent.numerator (var 1)) (var 4)) ⟶
      independentRate eulerF gammaF (eulerData (var 0) (var 1) (var 2) (var 3) (var 4))
        (gammaData (var 0) (var 1) (var 2) (var 3))
        (coefficientNumerator (var 1) (var 3)) (coefficientDenominator (var 1) one (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (original_right_half_plane_euler_rate _ _ _ _ _
    hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaRightHalfPlane
