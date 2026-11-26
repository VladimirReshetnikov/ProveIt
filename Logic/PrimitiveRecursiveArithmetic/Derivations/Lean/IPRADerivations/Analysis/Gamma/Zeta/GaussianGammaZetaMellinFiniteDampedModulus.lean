import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinFiniteDampedEvaluator

/-!
# A sampled modulus for the original finite damped prefix

Both read clocks amortize all row observation errors. The spatial
coefficient is the number of rows times the largest admitted
positive-scale Euler modulus.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (inside value sampledModulus evaluatorName nameData)
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinFiniteDampedEvaluator (rawBody rawData evaluatorF data evaluator_at raw_term_at subst_rawData subst_data)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "dampL" => GaussianEulerDampedTimeRate.lipschitz
local notation "Damped" => GaussianEulerPositiveScalingIntegrand.evaluatorF

def lipschitz (N R E T : PTm n) : PTm n := N*dampL R E T N one

@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (N R E T : PTm n) :
    Syn.subst σ (lipschitz N R E T) =
      lipschitz (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by simp [lipschitz,one]

private theorem row_lipschitz (c N R E T : PTm n) (h : Γ ⊢[PRAAx] le c N) :
    Γ ⊢[PRAAx] le (dampL R E T c one) (dampL R E T N one) := by
  have base : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by
    unfold num
    ipra_le 2
  have g : Γ ⊢[PRAAx] le (GaussianEulerDampedTimeRate.decayBound T c) (GaussianEulerDampedTimeRate.decayBound T N) :=
    GaussianFactorBudget.power_monotone_length _ _ _ base (mul_le_mul_right T h)
  unfold GaussianEulerDampedTimeRate.lipschitz GaussianEulerDampedTimeRate.decayLipschitz
  exact add_le_add₂ (mul_le_mul_right _ g) (le_mul_mono (le_refl _) (le_mul_mono g h))

theorem original_modulus_at (z R B N Q a C E T p q t u A D : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hQ : Γ ⊢[PRAAx] le N Q)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A D) : Γ ⊢[PRAAx]
    distanceBounded (ap3 evaluatorF p t (data z B N Q)) (ap3 evaluatorF q u (data z B N Q))
      (rateNumerator (lipschitz N R E T*A) D p q) (rateDenominator D p q) := by
  let s := exponent Q p
  let v := exponent Q q
  let L := dampL R E T N one
  let x := rawData s t z B
  let y := rawData v u z B
  let K := rateNumerator (L*A) D s v
  let V := rateDenominator D s v
  have hV := GaussianNamedInverseRate.denominator_positive D s v hD
  have rows : Γ ⊢[PRAAx] termsDistance rawBody rawBody N x y K V := by
    refine .allI (.impI ?_)
    let sh (j : PTm n) := Syn.shift j
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    let c := succ i
    have hs : Δ ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) := by
      simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift.wk
    have hDs : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hD.shift.wk
    have ht' : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) (sh t) := by
      simpa [Fm.shift,Syn.shift,Δ,sh] using ht.shift.wk
    have hu' : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) (sh u) := by
      simpa [Fm.shift,Syn.shift,Δ,sh] using hu.shift.wk
    have hd' : Δ ⊢[PRAAx] distanceBounded (value (sh t)) (value (sh u)) (sh A) (sh D) := by
      simpa [Fm.shift,Syn.shift,Δ,sh] using hd.shift.wk
    have hc : Δ ⊢[PRAAx] le c (sh N) := Prf.hyp0
    have source : Δ ⊢[PRAAx] GaussianEulerDampedCompactName.source (sh z) (sh R) (sh B) c one
        (sh a) (sh C) (sh E) (sh T) :=
      .andI hs (.andI (zero_lt_succ i) (le_refl one))
    have w := GaussianEulerDampedCompactName.sampled_modulus _ _ _ _ _ _ _ _ _ source
    have z' := GaussianCompactRiemannName.sampled_modulus_at Damped (sh a) (sh C) (sh E) _ _ (sh s) (sh v)
      (sh t) (sh u) (sh A) (sh D) w hDs ht' hu' hd'
    have g := mul_le_mul_right (sh A*unit (sh s)*unit (sh v))
      (row_lipschitz c (sh N) (sh R) (sh E) (sh T) hc)
    have hv := GaussianNamedInverseRate.denominator_positive (sh D) (sh s) (sh v) hDs
    have hR : Δ ⊢[PRAAx] le
        (rateNumerator (dampL (sh R) (sh E) (sh T) c one*sh A) (sh D) (sh s) (sh v)*
          rateDenominator (sh D) (sh s) (sh v))
        (rateNumerator (dampL (sh R) (sh E) (sh T) (sh N) one*sh A) (sh D) (sh s) (sh v)*
          rateDenominator (sh D) (sh s) (sh v)) := by
      let d := rateDenominator (sh D) (sh s) (sh v)
      have added := add_le_add_right (sh D*(unit (sh s)+unit (sh v))) g
      exact mul_le_mul_right d (le_congr (by unfold rateNumerator; ipra_ring) (by unfold rateNumerator; ipra_ring) added)
    have moved := distance_radius_mono _ _ _ _ _ _ hv hv hR z'
    have e1 := raw_term_at (Γ := Δ) i (sh s) (sh t) (sh z) (sh B)
    have e2 := raw_term_at (Γ := Δ) i (sh v) (sh u) (sh z) (sh B)
    simpa only [x,y,K,V,L,s,v,sh,Δ,i,c,Syn.shift,subst_rawData,
      GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,PTm.subst_mul,
      GaussianFastValueCut.subst_exponent,GaussianEulerDampedTimeRate.subst_lipschitz,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      distance_congr e1.eqSymm e2.eqSymm (.eqRefl _) (.eqRefl _) moved
  have d := sum_distance rawBody rawBody N x y K V hV rows
  have hBase := GaussianNamedInverseRate.denominator_positive D p q hD
  have pBudget : Γ ⊢[PRAAx] le (N*unit p) (unit s) :=
    le_trans (mul_le_mul_right (unit p) hQ) (query_budget Q p)
  have qBudget : Γ ⊢[PRAAx] le (N*unit q) (unit v) :=
    le_trans (mul_le_mul_right (unit q) hQ) (query_budget Q q)
  have eq : Γ ⊢[PRAAx] le ((N*K)*rateDenominator D p q) ((rateNumerator (lipschitz N R E T*A) D p q)*V) := by
    change Γ ⊢[PRAAx] le
      ((N*(L*A*unit s*unit v+D*(unit s+unit v)))*(D*unit p*unit q))
      (((N*L*A)*unit p*unit q+D*(unit p+unit q))*(D*unit s*unit v))
    ipra_le 𝔞(D)*𝔞(D)*𝔞(unit p)*𝔞(unit s)*sl qBudget + 𝔞(D)*𝔞(D)*𝔞(unit q)*𝔞(unit v)*sl pBudget
  exact distance_congr (evaluator_at p t z B N Q).eqSymm (evaluator_at q u z B N Q).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hV hBase eq d)

private theorem local_rate (z R B N Q a C E T t u A D : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hQ : Γ ⊢[PRAAx] le N Q)
    (hD : Γ ⊢[PRAAx] le one D) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) A D) : Γ ⊢[PRAAx]
    independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (data z B N Q)) (nameData u (data z B N Q)) (lipschitz N R E T*A) D := by
  refine .allI (.allI ?_)
  let sh (j : PTm n) := Syn.shift (Syn.shift j)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h' : Δ ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift.shift
  have hQ' : Δ ⊢[PRAAx] le (sh N) (sh Q) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hQ.shift.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hD.shift.shift
  have ht' : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) (sh t) := by simpa [Fm.shift,Syn.shift,Δ,sh] using ht.shift.shift
  have hu' : Δ ⊢[PRAAx] inside (sh a) (sh C) (sh E) (sh u) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hu.shift.shift
  have hd' : Δ ⊢[PRAAx] distanceBounded (value (sh t)) (value (sh u)) (sh A) (sh D) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hd.shift.shift
  have raw := original_modulus_at (sh z) (sh R) (sh B) (sh N) (sh Q) (sh a) (sh C) (sh E) (sh T) (var 1) (var 0)
    (sh t) (sh u) (sh A) (sh D) h' hQ' hD' ht' hu' hd'
  have left := GaussianCompactRiemannName.evaluator_at (Γ := Δ) evaluatorF (var 1) (sh t) (data (sh z) (sh B) (sh N) (sh Q))
  have right := GaussianCompactRiemannName.evaluator_at (Γ := Δ) evaluatorF (var 0) (sh u) (data (sh z) (sh B) (sh N) (sh Q))
  simpa only [independentRate,Δ,sh,Syn.shift,GaussianCompactRiemannName.subst_nameData,subst_data,subst_lipschitz,PTm.subst_mul]
    using distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem original_sampled_modulus (z R B N Q a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hQ : Γ ⊢[PRAAx] le N Q) : Γ ⊢[PRAAx]
    sampledModulus evaluatorF a C E (lipschitz N R E T) (data z B N Q) := by
  let sh (j : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift j)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have h' : Δ ⊢[PRAAx] intervalSource (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,Function.comp_assoc] using h.shift.shift.shift.shift
  have hQ' : Δ ⊢[PRAAx] le (sh N) (sh Q) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,Function.comp_assoc] using hQ.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [GaussianCompactRiemannName.localBody,subst_lipschitz,subst_data,Syn.shift,sh] using
    local_rate (sh z) (sh R) (sh B) (sh N) (sh Q) (sh a) (sh C) (sh E) (sh T) (var 3) (var 2) (var 1) (var 0)
      h'.wk.wk.wk.wk hQ'.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedModulus
