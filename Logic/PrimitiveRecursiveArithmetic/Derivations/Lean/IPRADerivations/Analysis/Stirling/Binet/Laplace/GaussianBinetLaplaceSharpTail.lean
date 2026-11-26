import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceStripTailEnvelope
import IPRADerivations.Analysis.Integration.GaussianCompactZeroWidth

/-!
# The sharp real exponential bound for the actual Binet tail

The endpoint is read from the original nonnegative real exponential
representative at an independent precision. This statement keeps its
exact rational value and displays the two observation allowances.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceSharpTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceDomination (realDecay realNumerator realDenominator nonnegative_real_radius)
open GaussianBinetLaplaceStrip (Kernel evaluatorF nameF data source subst_data fixedData)
open GaussianBinetLaplaceStripTail (tailNumerator tailDenominator)
open GaussianBinetLaplaceStripTailEnvelope (strip_endpoint_observation_bound)
open GaussianBinetLaplaceIntegrand (meshGain)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_nonnegative sample_canonical)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "twelve" => num 12

theorem zero_width (K : Kernel) (p X Y D sign R T N A C E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] C ≐ zero) :
    Γ ⊢[PRAAx] ap2 (nameF K) p (data X Y D sign R T N A C E) ≐ qzero := by
  have same : Γ ⊢[PRAAx] data X Y D sign R T N A C E ≐ data X Y D sign R T N A zero E := by
    simpa only [subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1
        (data (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift R) (Syn.shift T)
          (Syn.shift N) (Syn.shift A) (var 0) (Syn.shift E)) hC
  exact (congrAp2 (nameF K) (.eqRefl p) same).eqTrans
    (GaussianCompactZeroWidth.observation_zero (evaluatorF K) p (E+A) E (meshGain R T) T (fixedData X Y D sign R T N) hE)

theorem positive_decay_observation (q a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    let z := realDecay q a b
    Γ ⊢[PRAAx] bounded (observation a b q)
      (realNumerator z*unit q+two*realDenominator z) (realDenominator z*unit q) := by
  dsimp only
  let z := realDecay q a b
  let M := realNumerator z
  let E := realDenominator z
  let U := unit q
  have hd : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive _
  have hu := unit_positive (Γ := Γ) q
  have hr := nonnegative_real_radius z M E (sample_nonnegative (signedTime a b) q)
    (sample_canonical (signedTime a b) q) hd (le_congr (mul_comm M E) (.eqRefl _) (le_refl (M*E)))
  have d := GaussianNameEquivalence.cross_at decayF positiveF (decayData a b) (positiveData (signedTime a b)) q q
    (GaussianNameEquivalence.cross_symm _ _ _ _ (original_decay_nonnegative_representative a b hb))
  have near := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ two U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) d
  exact bound_congr (.eqRefl _) (by ipra_ring) (mul_comm U E)
    (GaussianReconstructionRoots.norm_from_distance _ _ two U M E hu hd near hr)

def endpointNumerator (q a b : PTm n) : PTm n :=
  realNumerator (realDecay q a b)*unit q+num 3*realDenominator (realDecay q a b)

def endpointDenominator (q a b : PTm n) : PTm n :=
  realDenominator (realDecay q a b)*unit q

/-- If `e_q` is the displayed sample of the nonnegative original decay
at `XA/(DE)`, the actual integral observation has norm at most
`D/(12X) * (e_q+3/2^q)+1/2^p`, uniformly in the width. -/
theorem sharp_bound (p q X Y D sign R T N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF .cofinal) p (data X Y D sign R T N A C E))
      (tailNumerator p X D (endpointNumerator q (X*A) (D*E)) (endpointDenominator q (X*A) (D*E)))
      (tailDenominator p X (endpointDenominator q (X*A) (D*E))) := by
  let b := D*E
  let a := X*A
  let z := realDecay q a b
  let M := realNumerator z
  let F := realDenominator z
  let U := unit q
  let K := twelve*X
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have hF : Γ ⊢[PRAAx] le one F := RationalArgmin.denominator_positive _
  have hU := unit_positive (Γ := Γ) q
  have hQ := positive_product _ _ hF hU
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ h12 h.andE₁.andE₁.andE₁.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ (positive_product _ _ hK hQ) hp
  refine .orE (zero_or_succ C) ?_ ?_
  · exact bound_congr (zero_width .cofinal p X Y D sign R T N A C E h.wk.andE₂.andE₁ Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianMonicResidualRadius.zero_bounded _ _ hd.wk)
  · have hC : (C ≐ ConciseIPRA.PTm.succ (LeanProofs.IPRA.PTm.pred C))::Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    have raw := strip_endpoint_observation_bound p q X Y D sign R T N A C E
      (M*U+two*F) (F*U) h.wk hA.wk hC hQ.wk (positive_decay_observation q a b hb.wk)
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hK.wk
      (positive_product _ _ hQ.wk hU.wk)) hp.wk) hd.wk ?_ raw
    change _ ⊢[PRAAx] le
      (tailNumerator p X D ((M*U+two*F)*U+F*U) ((F*U)*U)*tailDenominator p X (F*U))
      (tailNumerator p X D (M*U+num 3*F) (F*U)*tailDenominator p X ((F*U)*U))
    exact le_of_eq_add (d := zero) (by dsimp only [tailNumerator,tailDenominator]; ipra_ring)

theorem actual_Binet_Laplace_sharp_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) (var 10) (var 11) ⟶ le one (var 9) ⟶
      bounded (ap2 (nameF .cofinal) (var 0)
        (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)))
        (tailNumerator (var 0) (var 2) (var 4)
          (endpointNumerator (var 1) (var 2*var 9) (var 4*var 11))
          (endpointDenominator (var 1) (var 2*var 9) (var 4*var 11)))
        (tailDenominator (var 0) (var 2) (endpointDenominator (var 1) (var 2*var 9) (var 4*var 11)))) :=
  closeUniv 12 (.impI (.impI (sharp_bound _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceSharpTail
