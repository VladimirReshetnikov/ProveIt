import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelLipschitz
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactPowerVariation
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison

/-!
# A degree-independent compact time modulus for original beta rows

The original power observations at both actual replacement clocks are
combined with the literal kernel's unit bound and Lipschitz constant one.
Every beta degree N>=T is allowed with the SAME compact time constant.
The conclusion is the actual sampledModulus contract used by the existing
lower-tail root-grid partition/refinement, on arbitrary positive encoded
times. No row modulus or beta-output bound is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelCompactModulus

open_ipra
open GaussianEulerExponentCompactBounds (source input)
open GaussianCompactLogarithmBounds (domain)
open GaussianBetaKernelGridComparison (row evaluatorF sampleDataBeta)
open GaussianBetaKernelExponential (kernel)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerCompactProductComparison (clock)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def lipschitz (R E T : PTm n) : PTm n := GaussianEulerCompactPowerVariation.lipschitz R E T+GaussianEulerCompactPowerMajorant.majorant R E T
def compactSource (z R B E T a C N : PTm n) : Fm PTm n :=
  source z R B E ⋏ ((le one N ⋏ le T N) ⋏ (le one a ⋏ le (a+C) (E*T)))
ipra_subst lipschitz [GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius]
ipra_subst compactSource

private theorem support (a b E T N : PTm n) (h : Γ ⊢[PRAAx] domain a b E T)
    (hN : Γ ⊢[PRAAx] le one N) (hTN : Γ ⊢[PRAAx] le T N) : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N :=
  .andI h.andE₁.andE₂ (.andI hN (le_trans h.andE₂.andE₂
    (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right b hTN))))

/-- Retain both actual replacement clocks, while coarsening only their
ordinary observation errors to the original requested p and q. -/
private theorem power_distance (p q z R B E T a b c d A D : PTm n)
    (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerF (clock p z B a b) (powerData z B a b))
      (ap2 powerF (clock q z B c d) (powerData z B c d))
      (rateNumerator (GaussianEulerCompactPowerVariation.lipschitz R E T*A) D p q) (rateDenominator D p q) := by
  let k := clock p z B a b
  let l := clock q z B c d
  have hD := h.andE₂.andE₂.andE₂.andE₁
  have old := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ k l
    (GaussianEulerCompactPowerVariation.original_power_rate z R B E T a b c d A D h)
  have first : Γ ⊢[PRAAx] le (unit p) (unit k) := GaussianExponentialReference.unit_monotone (GaussianEulerCompactProductComparison.clock_later p z B a b)
  have second : Γ ⊢[PRAAx] le (unit q) (unit l) := GaussianExponentialReference.unit_monotone (GaussianEulerCompactProductComparison.clock_later q z B c d)
  apply distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive D k l hD)
    (GaussianNamedInverseRate.denominator_positive D p q hD) _ old
  unfold rateNumerator rateDenominator
  ipra_le (𝔞 D*𝔞 D*𝔞(unit l)*𝔞(unit q))*sl first+(𝔞 D*𝔞 D*𝔞(unit k)*𝔞(unit p))*sl second

/-- Source-only local rate of the unchanged original beta rows, uniform
in numerical degree. The kernel introduces no observation-error factor. -/
theorem row_distance (p q z R B E T a b c d N A D : PTm n)
    (h : Γ ⊢[PRAAx] input z R B E T a b c d A D) (hN : Γ ⊢[PRAAx] le one N) (hTN : Γ ⊢[PRAAx] le T N) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (row q z B c d N)
      (rateNumerator (lipschitz R E T*A) D p q) (rateDenominator D p q) := by
  let k := clock p z B a b
  let l := clock q z B c d
  have hD := h.andE₂.andE₂.andE₂.andE₁
  have den := GaussianNamedInverseRate.denominator_positive D p q hD
  have us := support a b E T N h.andE₂.andE₁ hN hTN
  have vs := support c d E T N h.andE₂.andE₂.andE₁ hN hTN
  have kernelMetric := GaussianBetaKernelLipschitz.kernel_distance a b c d N A D us vs hD h.andE₂.andE₂.andE₂.andE₂
  have kernelCommon : Γ ⊢[PRAAx] distanceBounded (kernel a b N) (kernel c d N) (A*unit p*unit q) (rateDenominator D p q) :=
    distance_radius_mono _ _ _ _ _ _ hD den (le_of_eq_add (d := zero) (by unfold rateDenominator; ipra_ring)) kernelMetric
  have powerBound := GaussianEulerCompactPowerMajorant.original_power_observation l z R B E T c d h.andE₁ h.andE₂.andE₂.andE₁
  have product := GaussianNameArithmetic.product_distance _ _ _ _ _ _ _ one (GaussianEulerCompactPowerMajorant.majorant R E T) den
    (power_distance p q z R B E T a b c d A D h) kernelCommon (GaussianBetaKernelUnitBound.kernel_bound a b N us) powerBound
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold lipschitz rateNumerator; ipra_ring) (.eqRefl _) product

/-- No outer pair-code eta is needed: the original evaluator reads the
actual raw time fields, while only its constructed fixed data are decoded. -/
theorem evaluator_raw_at (p t z B N : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (sampleDataBeta z B N) ≐ row p z B (fstT t) (sndT t) N := by
  let x := sampleDataBeta z B N
  have program : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ GaussianBetaKernelGridComparison.betaTerm p t x := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (GaussianBetaKernelGridComparison.betaTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have zarg : Γ ⊢[PRAAx] fstT (fstT x) ≐ z := (congrFst (fst_pair (GaussianEulerIntegrandName.fixedData z B) N)).eqTrans (fst_pair z B)
  have barg : Γ ⊢[PRAAx] sndT (fstT x) ≐ B := (congrSnd (fst_pair (GaussianEulerIntegrandName.fixedData z B) N)).eqTrans (snd_pair z B)
  have lastInput : ![p,fstT (fstT x),sndT (fstT x),fstT t,sndT t,sndT x] (5 : Fin 6) = sndT x := rfl
  have lastOutput : ![p,z,B,fstT t,sndT t,N] (5 : Fin 6) = N := rfl
  apply program.eqTrans
  change Γ ⊢[PRAAx] row p (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (sndT x) ≐ row p z B (fstT t) (sndT t) N
  ipra_congr (row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [.eqRefl p, (show _ ⊢[PRAAx] fstT (fstT x) ≐ z from zarg), (show _ ⊢[PRAAx] sndT (fstT x) ≐ B from barg),
      .eqRefl (fstT t), .eqRefl (sndT t),
      (show _ ⊢[PRAAx] sndT x ≐ N from snd_pair (GaussianEulerIntegrandName.fixedData z B) N)] using [lastInput,
      lastOutput]

theorem wrapped_at (p t z B N : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianCompactRiemannName.evaluatorName evaluatorF) p (GaussianCompactRiemannName.nameData t (sampleDataBeta z B N)) ≐
      row p z B (fstT t) (sndT t) N :=
  (GaussianCompactRiemannName.evaluator_at _ p t _).eqTrans (evaluator_raw_at p t z B N)

theorem evaluator_rate (t u z R B E T N A D : PTm n)
    (h : Γ ⊢[PRAAx] input z R B E T (fstT t) (sndT t) (fstT u) (sndT u) A D)
    (hN : Γ ⊢[PRAAx] le one N) (hTN : Γ ⊢[PRAAx] le T N) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (sampleDataBeta z B N)) (GaussianCompactRiemannName.nameData u (sampleDataBeta z B N)) (lipschitz R E T*A) D := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
      (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))) (fstT (Syn.shift (Syn.shift u))) (sndT (Syn.shift (Syn.shift u)))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have ns : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hN.shift.shift
  have ts : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hTN.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianCompactRiemannName.subst_nameData,GaussianBetaKernelGridComparison.subst_sampleDataBeta,
    subst_lipschitz,PTm.subst_mul,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N))).eqSymm
      (.eqRefl _) (.eqRefl _) (row_distance (var 1) (var 0) _ _ _ _ _ _ _ _ _ _ _ _ hs ns ts)

theorem local_modulus_at (z R B E T a C N t u A D : PTm n) (hz : Γ ⊢[PRAAx] compactSource z R B E T a C N)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside a C E t)
    (hu : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) A D) : Γ ⊢[PRAAx]
    independentRate (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (sampleDataBeta z B N)) (GaussianCompactRiemannName.nameData u (sampleDataBeta z B N)) (lipschitz R E T*A) D :=
  evaluator_rate t u z R B E T N A D
    (.andI hz.andE₁ (.andI (GaussianEulerCompactAdditivity.domain_of_inside t a C E T hz.andE₂.andE₂.andE₁ hz.andE₁.andE₂.andE₁ hz.andE₂.andE₂.andE₂ ht)
      (.andI (GaussianEulerCompactAdditivity.domain_of_inside u a C E T hz.andE₂.andE₂.andE₁ hz.andE₁.andE₂.andE₁ hz.andE₂.andE₂.andE₂ hu) (.andI hD hd)))) hz.andE₂.andE₁.andE₁ hz.andE₂.andE₁.andE₂

theorem sampled_modulus (z R B E T a C N : PTm n) (h : Γ ⊢[PRAAx] compactSource z R B E T a C N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.sampledModulus evaluatorF a C E (lipschitz R E T) (sampleDataBeta z B N) := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      compactSource (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift N)))) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [GaussianCompactRiemannName.localBody,GaussianBetaKernelGridComparison.subst_sampleDataBeta,subst_lipschitz,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    local_modulus_at (Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift R))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift B)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift E))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift T)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
      (Syn.shift (Syn.shift (Syn.shift (Syn.shift C)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift N))))
      (var 3) (var 2) (var 1) (var 0) hs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (z R B E T a C N : PTm n) (h : Γ ⊢[PRAAx] compactSource z R B E T a C N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannName.input evaluatorF a C E (lipschitz R E T) T (sampleDataBeta z B N) :=
  .andI h.andE₂.andE₂.andE₁ (.andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₂.andE₂.andE₂) (sampled_modulus z R B E T a C N h)))

theorem original_beta_compact_row_independent_precision_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    ((input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 12) (var 13) ⋏ le one (var 11) ⋏ le (var 6) (var 11)) ⟶
      distanceBounded (row (var 0) (var 2) (var 4) (var 7) (var 8) (var 11)) (row (var 1) (var 2) (var 4) (var 9) (var 10) (var 11))
        (rateNumerator (lipschitz (var 3) (var 5) (var 6)*var 12) (var 13) (var 0) (var 1)) (rateDenominator (var 13) (var 0) (var 1))) :=
  closeUniv 14 (.impI (row_distance _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_beta_degree_independent_compact_sampled_modulus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (compactSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianCompactRiemannName.sampledModulus evaluatorF (var 5) (var 6) (var 3) (lipschitz (var 1) (var 3) (var 4)) (sampleDataBeta (var 0) (var 2) (var 7))) :=
  closeUniv 8 (.impI (sampled_modulus _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelCompactModulus
