import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerQuadraticKernelTimeRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAdditivity

/-!
# The genuine unfactored quadratic Euler kernel on a compact interval

The PR3 evaluator returns exactly the original kernelF/kernelData at
the native doubled parameter. Its original multiplication clock is
unchanged. Original disk/positive fraction/interval guards derive the
compact modulus, actual observation bound and regular quadrature name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerQuadraticKernelCompactName

open_ipra
open GaussianEulerSquareKernel (doubled kernelF kernelData)
open GaussianEulerPositiveScalingIntegrand (fixedData)
open GaussianCompactRiemannName (inside sampledModulus localBody)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem val_five {α : Type*} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def lipschitz (R E T c d : PTm n) : PTm n := GaussianEulerQuadraticKernelTimeRate.lipschitz (two*R) E T c d
def evaluatorTerm (p t x : PTm n) : PTm n := ap2 kernelF p
  (kernelData (doubled (fstT (fstT x)) (sndT (fstT x))) (sndT (fstT x))
    (fstT t) (sndT t) (fstT (sndT x)) (sndT (sndT x)))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))
def source (z R B c d a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a C E T ⋏ (le one c ⋏ le one d)
def data (z R B c d a C E T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a C E (lipschitz R E T c d) T (fixedData z B c d)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF

ipra_subst doubled
ipra_subst kernelData
ipra_subst lipschitz
ipra_subst evaluatorTerm
ipra_subst source
ipra_subst data

theorem evaluator_at (p t z B c d : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData z B c d) ≐ ap2 kernelF p (kernelData (doubled z B) B (fstT t) (sndT t) c d) := by
  have term : Γ ⊢[PRAAx] ap3 evaluatorF p t (fixedData z B c d) ≐ evaluatorTerm p t (fixedData z B c d) := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,fixedData z B c d]
  have left := fst_pair (Γ := Γ) (pairT z B) (pairT c d)
  have right := snd_pair (Γ := Γ) (pairT z B) (pairT c d)
  have hz := (congrFst left).eqTrans (fst_pair z B)
  have hB := (congrSnd left).eqTrans (snd_pair z B)
  have hc := (congrFst right).eqTrans (fst_pair c d)
  have hd := (congrSnd right).eqTrans (snd_pair c d)
  have dw : Γ ⊢[PRAAx] doubled (fstT (fstT (fixedData z B c d))) (sndT (fstT (fixedData z B c d))) ≐ doubled z B := by
    ipra_congr (doubled (var 0) (var 1) : PTm 2) with
      [(show _ ⊢[PRAAx] fstT (fstT (fixedData z B c d)) ≐ z from hz),
        (show _ ⊢[PRAAx] sndT (fstT (fixedData z B c d)) ≐ B from hB)]
  have fields : Γ ⊢[PRAAx] kernelData (doubled (fstT (fstT (fixedData z B c d))) (sndT (fstT (fixedData z B c d))))
      (sndT (fstT (fixedData z B c d))) (fstT t) (sndT t) (fstT (sndT (fixedData z B c d))) (sndT (sndT (fixedData z B c d))) ≐
      kernelData (doubled z B) B (fstT t) (sndT t) c d := by
    ipra_congr (kernelData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
      [(show _ ⊢[PRAAx] doubled (fstT (fstT (fixedData z B c d))) (sndT (fstT (fixedData z B c d))) ≐ doubled z B from dw),
        (show _ ⊢[PRAAx] sndT (fstT (fixedData z B c d)) ≐ B from hB), .eqRefl (fstT t), .eqRefl (sndT t),
        (show _ ⊢[PRAAx] fstT (sndT (fixedData z B c d)) ≐ c from hc),
        (show _ ⊢[PRAAx] sndT (sndT (fixedData z B c d)) ≐ d from hd)] using [val_five]
  exact term.eqTrans (congrAp2 kernelF (.eqRefl _) fields)

theorem wrapped_at (p t z B c d : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p (GaussianCompactRiemannName.nameData t (fixedData z B c d)) ≐
      ap2 kernelF p (kernelData (doubled z B) B (fstT t) (sndT t) c d) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t z B c d)

theorem evaluator_observation_bound (p t z R B E T c d : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerSquareTimeGeometry.source z R B E c d)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (fstT t) (sndT t) E T) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p t (fixedData z B c d)) (GaussianEulerQuadraticKernelTimeRate.majorant (two*R) E T c) one :=
  GaussianRationalReciprocal.bound_congr (evaluator_at p t z B c d).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerQuadraticKernelTimeRate.original_observation_bound p (doubled z B) (two*R) B E T c d (fstT t) (sndT t)
      (GaussianEulerQuadraticKernelTimeRate.doubled_source z R B E c d h) ht)

theorem local_modulus_at (z R B c d a C E T t u A D : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData z B c d)) (GaussianCompactRiemannName.nameData u (fixedData z B c d)) (lipschitz R E T c d*A) D := by
  have hz := GaussianEulerQuadraticKernelTimeRate.doubled_source z R B E c d (.andI h.andE₁.andE₁ h.andE₂)
  have ha := GaussianEulerCompactAdditivity.domain_of_inside t a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ ht
  have hb := GaussianEulerCompactAdditivity.domain_of_inside u a C E T h.andE₁.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ hu
  have rate := GaussianEulerQuadraticKernelTimeRate.original_rate (doubled z B) (two*R) B E T c d
    (fstT t) (sndT t) (fstT u) (sndT u) A D hz ha hb hD near
  let sh := fun x : PTm n => Syn.shift (Syn.shift x)
  apply GaussianNamedInverseRate.transport_by_sample_eq rate
  · simpa [sh, Syn.shift] using wrapped_at (var 1) (sh t) (sh z) (sh B) (sh c) (sh d)
  · simpa [sh, Syn.shift] using wrapped_at (var 0) (sh u) (sh z) (sh B) (sh c) (sh d)

theorem sampled_modulus (z R B c d a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz R E T c d) (fixedData z B c d) := by
  let sh := fun x : PTm n => Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      source (sh z) (sh R) (sh B) (sh c) (sh d) (sh a) (sh C) (sh E) (sh T) := by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,GaussianEulerPositiveScalingIntegrand.subst_fixedData,subst_lipschitz,Syn.shift,sh] using
    local_modulus_at (sh z) (sh R) (sh B) (sh c) (sh d) (sh a) (sh C) (sh E) (sh T)
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

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

theorem actual_unfactored_quadratic_Euler_kernel_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (name_regular _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerQuadraticKernelCompactName
