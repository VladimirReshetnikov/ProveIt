import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# Actual compact quadrature names for positive rational Euler damping

The unchanged positive-scaling PR3 client evaluates the original power
at t and the original decay at (c/d)t. All interval guards are numerical;
the proved compact rate supplies its actual sampled modulus internally.
Arbitrary positive starting numerators and zero widths are allowed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDampedCompactName

open_ipra
open GaussianEulerPositiveScalingIntegrand (evaluatorF fixedData dampedF dampedData)
open GaussianEulerDampedTimeRate (lipschitz)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (distanceBounded)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B c d a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a C E T ⋏ (le one c ⋏ le one d)
def data (z R B c d a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R E T c d) T (fixedData z B c d)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

ipra_subst source
ipra_subst data

private theorem fixed_data_congr (z B a b c d z' B' c' d' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B') (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    dampedData z B a b c d ≐ dampedData z' B' a b c' d' := by
  have e1 : Γ ⊢[PRAAx] dampedData z B a b c d ≐ dampedData z' B a b c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_dampedData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (dampedData (var 0) (Syn.shift B) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hz
  have e2 : Γ ⊢[PRAAx] dampedData z' B a b c d ≐ dampedData z' B' a b c d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_dampedData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (dampedData (Syn.shift z') (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d)) hB
  have e3 : Γ ⊢[PRAAx] dampedData z' B' a b c d ≐ dampedData z' B' a b c' d := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_dampedData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (dampedData (Syn.shift z') (Syn.shift B') (Syn.shift a) (Syn.shift b) (var 0) (Syn.shift d)) hc
  have e4 : Γ ⊢[PRAAx] dampedData z' B' a b c' d ≐ dampedData z' B' a b c' d' := by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_dampedData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (dampedData (Syn.shift z') (Syn.shift B') (Syn.shift a) (Syn.shift b) (Syn.shift c') (var 0)) hd
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans e4))

theorem evaluator_raw_at (p t z B c d : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B c d) ≐ ap2 dampedF p (dampedData z B (fstT t) (sndT t) c d) := by
  have left := fst_pair (Γ := Γ) (pairT z B) (pairT c d)
  have right := snd_pair (Γ := Γ) (pairT z B) (pairT c d)
  exact (GaussianEulerPositiveScalingIntegrand.evaluator_at p t (fixedData z B c d)).eqTrans
    (congrAp2 dampedF (.eqRefl _) (fixed_data_congr _ _ _ _ _ _ _ _ _ _
      left.fstE left.sndE
      right.fstE right.sndE))

theorem wrapped_at (p t z B c d : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p (GaussianCompactRiemannName.nameData t (fixedData z B c d)) ≐
      ap2 dampedF p (dampedData z B (fstT t) (sndT t) c d) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_raw_at p t z B c d)

theorem local_modulus_at (z R B c d a C E T t u A D : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B c d)) (GaussianCompactRiemannName.nameData u (fixedData z B c d))
      (lipschitz R E T c d*A) D := by
  have raw := GaussianEulerDampedTimeRate.original_rate z R B E T c d (fstT t) (sndT t) (fstT u) (sndT u) A D
    (.andI (.andI h.andE₁.andE₁ h.andE₂)
      (.andI (GaussianEulerCompactAdditivity.domain_of_inside t a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ ht)
        (.andI (GaussianEulerCompactAdditivity.domain_of_inside u a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ hu) (.andI hD hd))))
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  apply GaussianNamedInverseRate.transport_by_sample_eq raw
  · simpa [sh, Syn.shift] using wrapped_at (var 1) (sh t) (sh z) (sh B) (sh c) (sh d)
  · simpa [sh, Syn.shift] using wrapped_at (var 0) (sh u) (sh z) (sh B) (sh c) (sh d)

theorem sampled_modulus (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz R E T c d) (fixedData z B c d) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift c))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift d)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) := by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerPositiveScalingIntegrand.subst_fixedData,GaussianEulerDampedTimeRate.subst_lipschitz,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift c))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift d)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R E T c d) T (fixedData z B c d) :=
  .andI h.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₁.andE₂.andE₂) (sampled_modulus z R B c d a C E T h)))

theorem name_regular (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B c d a C E T) :=
  GaussianCompactRiemannName.name_regular evaluatorF _ _ _ _ _ _ (compact_input z R B c d a C E T h)

theorem name_at (p z R B c d a C E T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B c d a C E T) ≐ GaussianCompactRiemannName.quadrature evaluatorF
      (GaussianCompactRiemannName.precision p T) (GaussianCompactRiemannName.mesh p (lipschitz R E T c d) T)
      a C E (fixedData z B c d) := GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem actual_damped_Euler_sampled_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      sampledModulus evaluatorF (var 5) (var 6) (var 7) (lipschitz (var 1) (var 7) (var 8) (var 3) (var 4)) (fixedData (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 9 (.impI (sampled_modulus _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_damped_Euler_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (name_regular _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDampedCompactName
