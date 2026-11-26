import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.DerivativeQuotients.GaussianBinetLaplaceMomentForwardQuotient
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.DerivativeQuotients.GaussianBinetLaplaceMomentMarginBound

/-!
# The original forward moment quotient at a fixed positive margin

For a base fraction X/D with D ≤ K X, the Taylor coefficient uses
only K and the moment order. In particular it applies to later
observations whose encoding denominators need not stay bounded.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentForwardMargin

open_ipra
open GaussianBinetLaplaceMomentForwardQuotient
  (quotientF quotientData targetF targetData samplerBudget quotient_regular positive_parameter sample_of_taylor)
open GaussianBinetLaplaceMomentImproper (nameF data regular sample_canonical)
open GaussianBinetLaplaceMomentImproperTaylor (observation_taylor_with_cap)
open GaussianBinetLaplaceMomentMarginBound (marginBound observation_bound)
open GaussianDominantPairAlgebra (radiusNumerator)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNameRingLaws (negative_fast)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def source (X D R K H Q : PTm n) : Fm PTm n :=
  realSource X zero D zero R ⋏ ((le one K ⋏ le D (K*X)) ⋏
    (le one H ⋏ (le one Q ⋏ le H Q)))

def cap (j K : PTm n) : PTm n := marginBound (succ (succ j)) K

def linearBudget (j K H : PTm n) : PTm n := num 3*H*(cap j K+num 3)

abbrev upperRadius (X D H Q : PTm n) : PTm n := radius (X*Q+H*D) zero

ipra_subst source [one]

ipra_subst cap

ipra_subst linearBudget

theorem upper_source (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] realSource (X*Q+H*D) zero (D*Q) zero (upperRadius X D H Q) :=
  source_of_right_half_plane _ _ _ _
    (.andI (.andI (le_trans (positive_product _ _ h.andE₁.andE₁.andE₁ hQ) (le_add_right _ _)) (.orI₁ (.eqRefl zero)))
      (positive_product _ _ h.andE₁.andE₂ hQ))

theorem observation (p j X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData j X D R (upperRadius X D H Q) H Q))
      (ap2 targetF p (targetData j X D R))
      (diagonalNumerator (linearBudget j K H) Q (samplerBudget j X D R (upperRadius X D H Q) H Q) p)
      (diagonalDenominator Q p) := by
  let S := upperRadius X D H Q
  have hBase := h.andE₁
  have hH := h.andE₂.andE₂.andE₁
  have hQ := h.andE₂.andE₂.andE₂.andE₁
  have hEnd := upper_source X D R H Q hBase hQ
  have cert : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input nameF nameF
      (data j (X*Q+H*D) (D*Q) S) (data j X D R) (radiusNumerator H) Q :=
    .andI (regular _ _ _ _ hEnd) (.andI (regular _ _ _ _ hBase) (positive_parameter H Q hH hQ))
  exact sample_of_taylor p _ _ _ H Q (cap j K+num 3) (num 10) cert
    (regular (succ j) X D R hBase) (sample_canonical p (succ j) X D R) hH hQ
    (observation_taylor_with_cap p j X D R S H Q (cap j K) hBase hEnd hQ h.andE₂.andE₂.andE₂.andE₂
      (observation_bound p (succ (succ j)) X D R K hBase h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂))

theorem forward_rate (j X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    Γ ⊢[PRAAx] independentRate quotientF targetF
      (quotientData j X D R (upperRadius X D H Q) H Q) (targetData j X D R) (linearBudget j K H) Q := by
  let S := upperRadius X D H Q
  have hQ := h.andE₂.andE₂.andE₂.andE₁
  apply GaussianNamedLipschitzRate.independent_rate quotientF targetF
    (quotientData j X D R S H Q) (targetData j X D R) (linearBudget j K H) Q (samplerBudget j X D R S H Q) hQ
    (quotient_regular j X D R S H Q h.andE₁ (upper_source X D R H Q h.andE₁ hQ) h.andE₂.andE₂.andE₁ hQ)
    (negative_fast _ _ (regular (succ j) X D R h.andE₁))
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh X) (sh D) (sh R) (sh K) (sh H) (sh Q) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEnvelope, Syn.shift, sh, Δ, GaussianBinetLaplaceMomentForwardQuotient.subst_quotientData,
    GaussianBinetLaplaceMomentForwardQuotient.subst_targetData, GaussianBinetLaplaceMomentForwardQuotient.subst_samplerBudget,
    subst_linearBudget, S, GaussianLogGammaEulerResidualRadius.subst_radius, PTm.subst_add, PTm.subst_mul,
    ConciseIPRA.PTm.subst_zero] using observation (var 0) (sh j) (sh X) (sh D) (sh R) (sh K) (sh H) (sh Q) hs

theorem actual_original_Binet_moment_forward_quotient_with_margin_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let j := var 0
       let X := var 1
       let D := var 2
       let R := var 3
       let K := var 4
       let H := var 5
       let Q := var 6
       source X D R K H Q ⟶ independentRate quotientF targetF (quotientData j X D R (upperRadius X D H Q) H Q)
         (targetData j X D R) (linearBudget j K H) Q) :=
  closeUniv 7 (.impI (forward_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentForwardMargin
