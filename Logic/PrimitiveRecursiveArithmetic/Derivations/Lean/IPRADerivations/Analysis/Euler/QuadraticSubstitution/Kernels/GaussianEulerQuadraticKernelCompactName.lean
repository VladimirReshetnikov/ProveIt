import IPRADerivations.Analysis.Euler.QuadraticSubstitution.Kernels.GaussianEulerQuadraticKernelTimeRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity

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
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 1)
    (ap2 kernelF (var 0) (kernelData (doubled (fstT (var 2)) (sndT (var 2))) (sndT (var 2))
        (fstT (var 1)) (sndT (var 1)) (fstT (var 3)) (sndT (var 3)))) p t ![pairT z B, pairT c d]
  simp only [subst_ap2, subst_kernelData, subst_doubled, subst_fstT, subst_sndT, Syn.subst_var] at read
  refine read.eqTrans (congrAp2 kernelF (.eqRefl p) ?_)
  ipra_congr (kernelData (doubled (var 0) (var 1)) (var 1) (fstT (var 2)) (sndT (var 2))
    (var 3) (var 4) : PTm 5) with
    [fst_pair z B, snd_pair z B, .eqRefl t, fst_pair c d, snd_pair c d]

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
