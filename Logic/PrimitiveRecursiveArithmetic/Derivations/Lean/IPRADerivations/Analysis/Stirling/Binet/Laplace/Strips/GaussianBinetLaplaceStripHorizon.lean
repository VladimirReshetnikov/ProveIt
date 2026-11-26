import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStrip
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactClientIndependence

/-!
# Binet strip coherence across time horizons

A change of the exponential radius or the time horizon changes the
observation schedules. The original names remain equivalent on a
physical panel that belongs to both charts.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripHorizon

open_ipra
open GaussianBinetLaplaceIntegrand (input subst_input meshGain)
open GaussianBinetLaplaceStrip
  (Kernel integrandF integrandData evaluatorF fixedData tagNumerator tag_inside wrapped_at compact_input source subst_source)
open GaussianCompactRiemannName (inside evaluatorName nameData)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal)
open GaussianNameArithmetic (multiplyF multiplyData)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data

private theorem same_kernel (K : PR 2) (x y k : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN ExpF x) (hy : Γ ⊢[PRAAx] pointCN ExpF y) (hk : Γ ⊢[PRAAx] pointCN K k)
    (he : Γ ⊢[PRAAx] crossEquivalent ExpF ExpF x y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF ExpF K) (multiplyF ExpF K) (multiplyData ExpF K x k) (multiplyData ExpF K y k) :=
  GaussianNameArithmetic.multiply_equivalent ExpF ExpF K K x y k k hx hy hk hk
    (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ (cross_refl K k hk))

theorem integrand_coherence (K : Kernel) (X Y D sign R T S U N A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) (h' : Γ ⊢[PRAAx] input X Y D sign S U A B) :
    Γ ⊢[PRAAx] crossEquivalent (integrandF K) (integrandF K)
      (integrandData K X Y D sign R T N A B) (integrandData K X Y D sign S U N A B) := by
  let q := GaussianBinetLaplaceExponential.exponent X Y D sign A B
  let x := expData X Y D sign R T A B
  let y := expData X Y D sign S U A B
  have hB := h.andE₂.andE₁
  have hx := GaussianSignedNameExponentialOrder.constant_input q (R*T)
    (GaussianBinetLaplaceExponential.exponent_bound X Y D sign R T A B h.andE₁ hB h.andE₂.andE₂)
  have hy := GaussianSignedNameExponentialOrder.constant_input q (S*U)
    (GaussianBinetLaplaceExponential.exponent_bound X Y D sign S U A B h'.andE₁ hB h'.andE₂.andE₂)
  have rx : Γ ⊢[PRAAx] pointCN ExpF x := GaussianRadiusExponentialName.name_regular constantF (R*T) q hx
  have ry : Γ ⊢[PRAAx] pointCN ExpF y := GaussianRadiusExponentialName.name_regular constantF (S*U) q hy
  have he : Γ ⊢[PRAAx] crossEquivalent ExpF ExpF x y :=
    GaussianExponentialRadiusIndependence.same_input_cross constantF (R*T) (S*U) q hx hy
  cases K
  · exact same_kernel GaussianBinetKernelTail.finiteF x y (GaussianBinetKernelTail.finiteData N A B) rx ry
      (GaussianNamedFiniteSumFamily.regular _ _ _ _ (GaussianBinetKernelRows.regular_rows N A B hB)) he
  · exact same_kernel GaussianBinetKernelCofinal.nameF x y (GaussianBinetKernelRows.inputData A B) rx ry
      (GaussianBinetKernelCofinal.regular A B hB) he

theorem evaluator_coherence (K : Kernel) (t X Y D sign R T S U N : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T (tagNumerator t) (sndT t))
    (h' : Γ ⊢[PRAAx] input X Y D sign S U (tagNumerator t) (sndT t)) :
    Γ ⊢[PRAAx] crossEquivalent (evaluatorName (evaluatorF K)) (evaluatorName (evaluatorF K))
      (nameData t (fixedData X Y D sign R T N)) (nameData t (fixedData X Y D sign S U N)) := by
  let s (z : PTm n) := Syn.shift (Syn.shift z)
  have he := integrand_coherence K X Y D sign R T S U N (tagNumerator t) (sndT t) h h'
  apply GaussianNameEquivalence.transport_by_sample_eq he
  · simpa [s, Syn.shift] using wrapped_at K (var 1) (s t) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N)
  · simpa [s, Syn.shift] using wrapped_at K (var 0) (s t) (s X) (s Y) (s D) (s sign) (s S) (s U) (s N)

private theorem panel_agreement_at (K : Kernel) (t X Y D sign R T S U N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (h' : Γ ⊢[PRAAx] source X Y D sign S U A C E)
    (ht : Γ ⊢[PRAAx] inside (E+A) C E t) :
    Γ ⊢[PRAAx] crossEquivalent (evaluatorName (evaluatorF K)) (evaluatorName (evaluatorF K))
      (nameData t (fixedData X Y D sign R T N)) (nameData t (fixedData X Y D sign S U N)) :=
  evaluator_coherence K t X Y D sign R T S U N
    (.andI h.andE₁ (.andI ht.andE₂.andE₁ (tag_inside t A C E T h.andE₂.andE₁ h.andE₂.andE₂ ht).andE₂))
    (.andI h'.andE₁ (.andI ht.andE₂.andE₁ (tag_inside t A C E U h'.andE₂.andE₁ h'.andE₂.andE₂ ht).andE₂))

theorem local_agreement (K : Kernel) (X Y D sign R T S U N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (h' : Γ ⊢[PRAAx] source X Y D sign S U A C E) :
    Γ ⊢[PRAAx] GaussianCompactClientIndependence.localAgreement (evaluatorF K) (evaluatorF K) (E+A) C E
      (fixedData X Y D sign R T N) (fixedData X Y D sign S U N) := by
  let s (z : PTm n) := Syn.shift z
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift
  have hs' : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s S) (s U) (s A) (s C) (s E) :=
    by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h'.shift
  refine .allI (.impI ?_)
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianCompactClientIndependence.agreementBody,
    GaussianCompactRiemannName.subst_sampleData,subst_pairT,PTm.subst_add,Syn.shift,s,Δ] using
    panel_agreement_at K (var 0) (s X) (s Y) (s D) (s sign) (s R) (s T) (s S) (s U) (s N) (s A) (s C) (s E)
      hs.wk hs'.wk Prf.hyp0

theorem coherence (K : Kernel) (X Y D sign R T S U N A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R T A C E) (h' : Γ ⊢[PRAAx] source X Y D sign S U A C E) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianBinetLaplaceStrip.nameF K) (GaussianBinetLaplaceStrip.nameF K)
      (GaussianBinetLaplaceStrip.data X Y D sign R T N A C E) (GaussianBinetLaplaceStrip.data X Y D sign S U N A C E) :=
  GaussianCompactClientIndependence.name_independence (evaluatorF K) (evaluatorF K) (E+A) C E (meshGain R T) T
    (meshGain S U) U (fixedData X Y D sign R T N) (fixedData X Y D sign S U N)
    (.andI (compact_input K X Y D sign R T N A C E h)
      (.andI (compact_input K X Y D sign S U N A C E h') (local_agreement K X Y D sign R T S U N A C E h h')))

theorem actual_Binet_strip_horizon_coherence_closed (K : Kernel) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 9) (var 10) (var 11) ⟶
        source (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) (var 9) (var 10) (var 11) ⟶
        crossEquivalent (GaussianBinetLaplaceStrip.nameF K) (GaussianBinetLaplaceStrip.nameF K)
          (GaussianBinetLaplaceStrip.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 8) (var 9) (var 10) (var 11))
          (GaussianBinetLaplaceStrip.data (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11))) :=
  closeUniv 12 (.impI (.impI (coherence K _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceStripHorizon
