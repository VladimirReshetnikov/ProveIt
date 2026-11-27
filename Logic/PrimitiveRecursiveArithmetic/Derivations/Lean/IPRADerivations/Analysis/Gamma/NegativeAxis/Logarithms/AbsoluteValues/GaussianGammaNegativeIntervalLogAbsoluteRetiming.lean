import IPRADerivations.Analysis.Gamma.NegativeAxis.Values.Apartness.GaussianGammaNegativeIntervalUniformLower
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.AbsoluteValues.GaussianGammaNegativeIntervalLogAbsolute
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.Euler.VerticalBounds.Projections.GaussianEulerVerticalProjection
import IPRADerivations.Analysis.Euler.VerticalBounds.Integrands.GaussianEulerVerticalRealSamples

/-!
# Positive logarithm of the retimed signed original negative Gamma

The signed Gamma name has a positive floor depending only on the
interval. The real projection preserves that floor, and retiming
retains samples whose exact values exceed half of it. The original
positive logarithm recovers the existing negative-interval log-absolute
name by real exponential injectivity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteRetiming

open_ipra
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalUniformLower (lowerDenominator signed_gamma_source)
open GaussianGammaRealValues (axisF axis_cross axis_sample_at projection)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "gd" => GaussianGammaNegativeIntervalLogAbsolute.nameData
local notation "E" => GaussianGammaNegativeIntervalLogAbsolute.expF
local notation "ed" => GaussianGammaNegativeIntervalLogAbsolute.expData

abbrev inputF : PR 2 := retimedF (axisF signedF)
def margin (N : PTm n) : PTm n := two*lowerDenominator N
def inputData (a b N : PTm n) : PTm n := retimedData (signedData a b N) (lowerDenominator N)
def radius (a b N : PTm n) : PTm n := U (axisF signedF) (signedData a b N)
abbrev nameF : PR 2 := GaussianNamedPositiveLogarithm.nameF inputF
def nameData (a b N : PTm n) : PTm n := GaussianNamedPositiveLogarithm.data (inputData a b N) (margin N)

private theorem subst_lower {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (lowerDenominator N) = lowerDenominator (Syn.subst σ N) := by
  simp [lowerDenominator,GaussianGammaNegativeIntervalUniformLower.productBound,GaussianStirlingGammaLogarithm.gammaMargin]

ipra_subst margin [subst_lower]
ipra_subst inputData [subst_lower]
ipra_subst radius
ipra_subst nameData

theorem input_at (p a b N : PTm n) : Γ ⊢[PRAAx]
    ap2 inputF p (inputData a b N) ≐ projection
      (ap2 signedF (p+GaussianNamedRightHalfPlane.threshold (lowerDenominator N)) (signedData a b N)) :=
  (GaussianNamedPositiveLateLogSource.sample_at (axisF signedF) p (signedData a b N) (lowerDenominator N)).eqTrans
    (axis_sample_at signedF _ (signedData a b N))

theorem positive_source (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source inputF (inputData a b N) (margin N) (radius a b N) :=
  GaussianNamedPositiveLateLogSource.positive_source _ _ _
    (GaussianEulerVerticalProjection.projected_source _ _ _ (signed_gamma_source a b N h))
    (GaussianEulerVerticalProjection.projected_real_samples signedF (signedData a b N))

private theorem exponential_fixed (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF E) E (ed a b N) (ed a b N) := by
  have regular := GaussianGammaNegativeIntervalLogAbsolute.exp_regular a b N h
  refine GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameConjugation.regular E (ed a b N) regular) regular (.allI ?_)
  let A := Syn.shift a
  let B := Syn.shift b
  let J := Syn.shift N
  let p : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have fixed : Δ ⊢[PRAAx] GaussianRationalConjugation.point (ap2 E p (ed A B J)) ≐ ap2 E p (ed A B J) :=
    GaussianEulerVerticalRealSamples.original_exponential_fixed G (U G (gd A B J)) (gd A B J) p
      (GaussianGammaNegativeIntervalLogAbsolute.name_real A B J)
  simpa only [GaussianNameConjugation.pointwiseEqual,GaussianGammaNegativeIntervalLogAbsolute.subst_expData,Syn.shift,A,B,J,p,Δ]
    using (GaussianNameConjugation.sample_at (Γ := Δ) E p (ed A B J)).eqTrans fixed

theorem signed_axis_cross (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent signedF (axisF signedF) (signedData a b N) (signedData a b N) := by
  let x := signedData a b N
  let z := ed a b N
  have ex := GaussianGammaNegativeIntervalLogAbsolute.original_exponential a b N h
  have conj := GaussianNameConjugation.conjugate_cross signedF E x z (cross_symm _ _ _ _ ex)
  exact axis_cross signedF x (signed_gamma_source a b N h).andE₁
    (cross_trans _ _ _ _ _ _ conj (cross_trans _ _ _ _ _ _ (exponential_fixed a b N h) ex))

theorem input_cross (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent signedF inputF (signedData a b N) (inputData a b N) :=
  cross_trans _ _ _ _ _ _ (signed_axis_cross a b N h)
    (GaussianNamedPositiveLateLogSource.original_cross _ _ _
      (GaussianEulerVerticalProjection.projected_source _ _ _ (signed_gamma_source a b N h)).andE₁)

theorem log_cross (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent G nameF (gd a b N) (nameData a b N) := by
  let x := inputData a b N
  let M := margin N
  let R := radius a b N
  let z := gd a b N
  have hs := positive_source a b N h
  have left := GaussianGammaFiniteApproximantName.exponential_input G z
    (GaussianGammaNegativeIntervalLogAbsolute.name_regular a b N h)
  have right := GaussianNamedPositiveLogarithm.exponential_input inputF x M R hs
  have recovery := GaussianNamedPositiveLogarithmExponential.original_recovery inputF x M R hs
  exact independent_radii_injective G nameF _ _ z (nameData a b N) left right
    (GaussianGammaNegativeIntervalLogAbsolute.name_axis a b N)
    (GaussianNamedPositiveLogarithm.real_samples inputF x M)
    (cross_trans _ _ _ _ _ _ (GaussianGammaNegativeIntervalLogAbsolute.original_exponential a b N h)
      (cross_trans _ _ _ _ _ _ (input_cross a b N h) (cross_symm _ _ _ _ recovery)))

theorem actual_original_negative_interval_retimed_log_absolute_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (guard (var 0) (var 1) ⟶
        (GaussianNamedPositiveLogarithm.source inputF (inputData (var 0) (var 1) (var 2)) (margin (var 2))
          (radius (var 0) (var 1) (var 2)) ⋏
          (crossEquivalent signedF inputF (signedData (var 0) (var 1) (var 2)) (inputData (var 0) (var 1) (var 2)) ⋏
            crossEquivalent G nameF (gd (var 0) (var 1) (var 2)) (nameData (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.andI (positive_source _ _ _ Prf.hyp0)
    (.andI (input_cross _ _ _ Prf.hyp0) (log_cross _ _ _ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteRetiming
