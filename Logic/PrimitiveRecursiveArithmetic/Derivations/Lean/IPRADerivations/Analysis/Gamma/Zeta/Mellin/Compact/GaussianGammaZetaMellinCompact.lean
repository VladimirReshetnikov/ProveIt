import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGrid
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinReciprocalRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactPowerVariation
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingPowerFrozen

/-!
# Regular compact quadrature for the original Mellin integrand

On a certified positive panel, combine the time moduli of the original
complex power and reciprocal. The resulting modulus applies to the
literal quadrature evaluator even when the rational tags use unrelated
denominators and the observation clocks are independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCompact

open_ipra
open GaussianCompactLogarithmBounds (domain)
open GaussianCompactRiemannName (inside localBody sampledModulus evaluatorName nameData)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData evaluator_at subst_fixedData)
open GaussianGammaZetaMellinIntegrand (reciprocalF reciprocalData denominatorF denominatorData)
open GaussianGammaZetaMellinReciprocalRate (reciprocal_samples reciprocal_rate)
open GaussianGammaZetaMellinStrip (window)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalMetric (distanceBounded)
open RationalValueBounds (positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianGammaZetaMellinIntegrand.nameF
local notation "fd" => GaussianGammaZetaMellinIntegrand.data
local notation "C" => GaussianEulerExponentCompactBounds.source

def gain (R H T : PTm n) : PTm n :=
  H*GaussianEulerCompactPowerVariation.lipschitz R H T+
    majorant R H T*GaussianGammaZetaMellinReciprocalRate.lipschitz H T

def source (z R B a W E H T : PTm n) : Fm PTm n := C z R B H ⋏ window a W E H T

abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF
def data (z R B a W E H T : PTm n) : PTm n :=
  GaussianCompactRiemannName.data a W E (gain R H T) T (fixedData z B)

@[simp] private theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R H T : PTm n) :
    Syn.subst σ (majorant R H T) = majorant (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ T) := by
  simp [majorant, GaussianEulerCompactPowerMajorant.exponentRadius, one]

ipra_subst gain

ipra_subst source

ipra_subst data

private theorem power_samples (z R B a b H T : PTm n)
    (hz : Γ ⊢[PRAAx] C z R B H) (ha : Γ ⊢[PRAAx] domain a b H T) :
    Γ ⊢[PRAAx] sampleBound powerF (powerData z B a b) (majorant R H T) := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] C (s z) (s R) (s B) (s H) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift
  have as' : Δ ⊢[PRAAx] domain (s a) (s b) (s H) (s T) := by simpa [Δ,s,Fm.shift,Syn.shift] using ha.shift
  simpa only [sampleBound,Syn.shift,s,GaussianEulerIntegrandName.subst_powerData,
    subst_majorant] using
    original_power_observation (var 0) (s z) (s R) (s B) (s H) (s T) (s a) (s b) zs as'

private theorem inverse_regular (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN reciprocalF (reciprocalData a b) :=
  GaussianNameReciprocal.name_fast denominatorF b (denominatorData a b)
    (GaussianGammaZetaMellinIntegrand.denominator_regular a b) (GaussianGammaZetaMellinIntegrand.denominator_apart a b ha hb)

theorem time_rate (z R B a b c d H T A D : PTm n)
    (hz : Γ ⊢[PRAAx] C z R B H) (ha : Γ ⊢[PRAAx] domain a b H T) (hc : Γ ⊢[PRAAx] domain c d H T)
    (hD : Γ ⊢[PRAAx] le one D) (time : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction c d) A D) :
    Γ ⊢[PRAAx] independentRate F F (fd z B a b) (fd z B c d) (gain R H T*A) D := by
  let U := GaussianEulerCompactPowerVariation.lipschitz R H T
  let V := GaussianGammaZetaMellinReciprocalRate.lipschitz H T
  have p := GaussianEulerCompactPowerVariation.original_power_rate z R B H T a b c d A D
    (.andI hz (.andI ha (.andI hc (.andI hD time))))
  have q := reciprocal_rate a b c d H T A D ha hc hD time
  have proof := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator powerF reciprocalF powerF reciprocalF
    (powerData z B a b) (reciprocalData a b) (powerData z B c d) (reciprocalData c d)
    (U*A) (V*A) D H (majorant R H T) hD
    (GaussianEulerIntegrandName.power_regular z B a b (.andI hz.andE₁ ha.andE₁))
    (inverse_regular a b ha.andE₁.andE₁ ha.andE₁.andE₂)
    (GaussianEulerIntegrandName.power_regular z B c d (.andI hz.andE₁ hc.andE₁))
    (inverse_regular c d hc.andE₁.andE₁ hc.andE₁.andE₂)
    (reciprocal_samples a b H T ha) (power_samples z R B c d H T hz hc) p q
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold gain U V; ipra_ring) (.eqRefl _) proof

theorem tag_domain (a W E H T t : PTm n) (hw : Γ ⊢[PRAAx] window a W E H T)
    (ht : Γ ⊢[PRAAx] inside a W E t) : Γ ⊢[PRAAx] domain (fstT t) (sndT t) H T := by
  let x := fstT t
  let y := sndT t
  have e := hw.andE₁.andE₂
  have low : Γ ⊢[PRAAx] le (E*y) (E*(H*x)) :=
    le_trans (mul_le_mul_right y hw.andE₂.andE₁)
      (le_congr (by ipra_ring) (by ipra_ring)
        (mul_le_mul_right H ht.andE₂.andE₂.andE₁))
  have high : Γ ⊢[PRAAx] le (E*x) (E*(T*y)) :=
    le_trans ht.andE₂.andE₂.andE₂
      (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right y hw.andE₂.andE₂))
  exact .andI (.andI ht.andE₁ ht.andE₂.andE₁)
    (.andI (positive_cancel e low) (positive_cancel e high))

private theorem wrapped_at (p t z B : PTm n) :
    Γ ⊢[PRAAx] ap2 (evaluatorName evaluatorF) p (nameData t (fixedData z B)) ≐
      ap2 F p (fd z B (fstT t) (sndT t)) := by
  let x := fixedData z B
  have read := (GaussianCompactRiemannName.evaluator_at (Γ := Γ) evaluatorF p t x).eqTrans (evaluator_at p t x)
  let body : PTm 5 := ap2 F (var 0) (fd (var 1) (var 2) (var 3) (var 4))
  let v : Fin 5 → PTm n := ![p,fstT x,sndT x,fstT t,sndT t]
  let w : Fin 5 → PTm n := ![p,z,B,fstT t,sndT t]
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) body (σ := v) (σ' := w) (fun i => by
    fin_cases i
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact snd_pair _ _
    · exact .eqRefl _
    · exact .eqRefl _)
  have left : Syn.subst v body = GaussianGammaZetaMellinGrid.evaluatorTerm p t x := by
    simp only [body,subst_ap2,GaussianGammaZetaMellinIntegrand.subst_data,Syn.subst_var]
    rfl
  have right : Syn.subst w body = ap2 F p (fd z B (fstT t) (sndT t)) := by
    simp only [body,subst_ap2,GaussianGammaZetaMellinIntegrand.subst_data,Syn.subst_var]
    rfl
  rw [left,right] at e
  exact read.eqTrans e

theorem local_rate (z R B a W E H T t u A D : PTm n) (hz : Γ ⊢[PRAAx] source z R B a W E H T)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a W E t) (hu : Γ ⊢[PRAAx] inside a W E u)
    (near : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData z B)) (nameData u (fixedData z B)) (gain R H T*A) D := by
  have rate := time_rate z R B (fstT t) (sndT t) (fstT u) (sndT u) H T A D hz.andE₁
    (tag_domain a W E H T t hz.andE₂ ht) (tag_domain a W E H T u hz.andE₂ hu) hD near
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  apply GaussianNamedInverseRate.transport_by_sample_eq rate
  · simpa [s, Syn.shift] using wrapped_at (var 1) (s t) (s z) (s B)
  · simpa [s, Syn.shift] using wrapped_at (var 0) (s u) (s z) (s B)

theorem sampled_modulus (z R B a W E H T : PTm n) (h : Γ ⊢[PRAAx] source z R B a W E H T) :
    Γ ⊢[PRAAx] sampledModulus evaluatorF a W E (gain R H T) (fixedData z B) := by
  let s (v : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift v)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s z) (s R) (s B) (s a) (s W) (s E) (s H) (s T) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,Δ,s,Syn.shift,subst_gain,subst_fixedData,PTm.subst_add] using
    local_rate (s z) (s R) (s B) (s a) (s W) (s E) (s H) (s T) (var 3) (var 2) (var 1) (var 0)
      hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B a W E H T : PTm n) (h : Γ ⊢[PRAAx] source z R B a W E H T) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF a W E (gain R H T) T (fixedData z B) :=
  .andI h.andE₂.andE₁.andE₁ (.andI h.andE₂.andE₁.andE₂
    (.andI (le_trans (le_add_left W a) (le_congr (.eqRefl _) (mul_comm T E) h.andE₂.andE₂.andE₂))
      (sampled_modulus z R B a W E H T h)))

theorem regular (z R B a W E H T : PTm n) (h : Γ ⊢[PRAAx] source z R B a W E H T) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B a W E H T) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input z R B a W E H T h)

theorem actual_original_Mellin_compact_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (regular _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinCompact
