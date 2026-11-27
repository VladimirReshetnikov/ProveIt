import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.UpperTails.GaussianGammaZetaMellinUpperGrid
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.FiniteRows.GaussianGammaZetaMellinFiniteDampedModulus
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGeometricEnvelope

/-!
# Uniform upper bound for the actual finite damped Mellin evaluator

At late enough precision the geometric comparison is absorbed into
the same inverse-square majorant as the original Mellin integrand.
The original scalar left-grid telescoper then yields an upper tail
independent of the number of damped rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedUpper

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at grid)
open GaussianEulerUpperPowerCoefficients (source)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF data budget comparisonClock geometric_point_error)
open GaussianGammaZetaMellinUpperPoint (coefficientBound degree upper_observation_bound)
open GaussianNamedDampingPowerReciprocalTail (body gridData subst_gridData affine_grid_majorant quadrature_bound_of_majorized)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized termsMajorized)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def coefficient (R : PTm n) : PTm n := two*coefficientBound R+one

ipra_subst coefficient [two, one]

theorem original_sample_bound (p z R B a b H T N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B a b)
    (hH : Γ ⊢[PRAAx] le one H) (hT : Γ ⊢[PRAAx] le a (T*b))
    (hp : Γ ⊢[PRAAx] le (degree R) p) (hlate : Γ ⊢[PRAAx] le (two*T*T) (unit p)) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF p (pairT a b) (data z B N (budget R H T N)))
      (coefficient R*(b*b)) (a*a) := by
  let s := comparisonClock p R H T N a b
  let V := unit p
  let K := coefficientBound R
  have ha := h.andE₂.andE₁.andE₁
  have hb := h.andE₂.andE₁.andE₂
  have hAA := positive_product _ _ ha ha
  have hV := unit_positive (Γ := Γ) p
  have modz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B H :=
    .andI h.andE₁.andE₁ (.andI hH h.andE₁.andE₂)
  have hD : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b H T :=
    .andI h.andE₂.andE₁ (.andI (le_trans h.andE₂.andE₂
      (le_congr (one_mul a) (.eqRefl _) (mul_le_mul_right a hH))) hT)
  have clock : Γ ⊢[PRAAx] le p s := le_trans (le_add_right _ _) (le_add_right _ _)
  have cmp := geometric_point_error p z R B a b H T N modz hD
  have original := upper_observation_bound s z R B a b h (le_trans hp clock)
  have prefixBound := GaussianGammaZetaMellinGeometricEnvelope.weighted_bound s z B a b N (K*(b*b)) (a*a) ha hb hAA original
  have combined := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hV hAA cmp prefixBound
  have squared : Γ ⊢[PRAAx] le (two*(a*a)) ((two*T*T)*(b*b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two (sq_le_sq hT))
  have absorb : Γ ⊢[PRAAx] le (two*(a*a)) (V*(b*b)) :=
    le_trans squared (mul_le_mul_right (b*b) hlate)
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hV hAA) hAA ?_ combined
  change Γ ⊢[PRAAx] le ((two*(a*a)+K*(b*b)*two*V)*(a*a))
    (((two*K+one)*(b*b))*(V*(a*a)))
  ipra_le 𝔞(a)*𝔞(a)*sl absorb

private theorem cell_majorant (i p M N z R B a C E H T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] le E a)
    (hC : Γ ⊢[PRAAx] le one C) (hM : Γ ⊢[PRAAx] le one M) (hH : Γ ⊢[PRAAx] le one H)
    (hi : Γ ⊢[PRAAx] lt i (C*M)) (hT : Γ ⊢[PRAAx] le (a+C) (T*E))
    (hp : Γ ⊢[PRAAx] le (degree R) p) (hLate : Γ ⊢[PRAAx] le (two*T*T) (unit p)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*M) a C E (data z B N (budget R H T N))))
      (inst2 body i (gridData (coefficient R) a E M)) := by
  let count := C*M
  let A := a*count+C*i
  let B₀ := E*count
  let x := data z B N (budget R H T N)
  let t := grid i count a C E
  let K := coefficient R
  have hB := positive_product E count hE (positive_product C M hC hM)
  have ht : Γ ⊢[PRAAx] le B₀ A := le_trans (mul_le_mul_right count ha) (le_add_right _ _)
  have hA := le_trans hB ht
  have top : Γ ⊢[PRAAx] le A (T*B₀) := by
    have hIndex : Γ ⊢[PRAAx] le i count := le_of_lt hi
    have room := add_le_add₂ (le_refl (a*count)) (le_mul_mono (le_refl C) hIndex)
    exact le_trans (le_congr (.eqRefl _) (by ipra_ring) room)
      (le_congr (.eqRefl _) (by dsimp only [B₀]; ipra_ring) (mul_le_mul_right count hT))
  have support : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B A B₀ :=
    .andI h (.andI (.andI hA hB) ht)
  have raw := original_sample_bound p z R B A B₀ H T N support hH top hp hLate
  have read := sample_body_at (Γ := Γ) evaluatorF i p count a C E x
  exact affine_grid_majorant i K a C E M A B₀ (le_trans hE ha) hC hM hA
    (.andI (fst_pair _ _) (snd_pair _ _)) read (bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _) raw)

theorem original_grid_bound (p M N z R B a C E H T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B) (hE : Γ ⊢[PRAAx] le one E) (ha : Γ ⊢[PRAAx] le E a)
    (hC : Γ ⊢[PRAAx] le one C) (hM : Γ ⊢[PRAAx] le one M) (hH : Γ ⊢[PRAAx] le one H) (hT : Γ ⊢[PRAAx] le (a+C) (T*E))
    (hp : Γ ⊢[PRAAx] le (degree R) p) (hLate : Γ ⊢[PRAAx] le (two*T*T) (unit p)) : Γ ⊢[PRAAx]
    bounded (quadrature evaluatorF p (C*M) a C E (data z B N (budget R H T N)))
      (two*coefficient R*E) a := by
  let count := C*M
  let f := sampleBody evaluatorF
  let X := sampleData p count a C E (data z B N (budget R H T N))
  let Y := gridData (coefficient R) a E M
  have hA := le_trans hE ha
  have rows : Γ ⊢[PRAAx] termsMajorized f body count X Y := by
    refine .allI (.impI ?_)
    let sh (x : PTm n) := Syn.shift x
    let Δ := lt (var 0) (sh C*sh M) :: Γ.map Fm.shift
    have hz : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.wk
    have hEs : Δ ⊢[PRAAx] le one (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hE.shift.wk
    have has : Δ ⊢[PRAAx] le (sh E) (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift] using ha.shift.wk
    have hCs : Δ ⊢[PRAAx] le one (sh C) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hC.shift.wk
    have hMs : Δ ⊢[PRAAx] le one (sh M) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hM.shift.wk
    have hHs : Δ ⊢[PRAAx] le one (sh H) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hH.shift.wk
    have hTs : Δ ⊢[PRAAx] le (sh a+sh C) (sh T*sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hT.shift.wk
    have hps : Δ ⊢[PRAAx] le (degree (sh R)) (sh p) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hp.shift.wk
    have hl : Δ ⊢[PRAAx] le (two*sh T*sh T) (unit (sh p)) := by
      simpa [Δ,sh,Fm.shift,Syn.shift,two,one] using hLate.shift.wk
    simpa only [Δ,sh,Syn.shift,f,X,Y,count,GaussianCompactRiemannName.subst_sampleData,
      GaussianGammaZetaMellinFiniteDampedEvaluator.subst_data,GaussianGammaZetaMellinFiniteDampedEvaluator.subst_budget,
      subst_gridData,subst_coefficient,PTm.subst_mul,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
      using cell_majorant (var 0) (sh p) (sh M) (sh N) (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh H) (sh T)
        hz hEs has hCs hMs hHs Prf.hyp0 hTs hps hl
  exact quadrature_bound_of_majorized evaluatorF p (coefficient R) a a C E M _ hA hC hE hM rows

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedUpper
