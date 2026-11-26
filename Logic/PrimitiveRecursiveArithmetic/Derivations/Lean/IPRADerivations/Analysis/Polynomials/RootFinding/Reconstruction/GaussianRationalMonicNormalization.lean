import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReciprocal

/-!
# Computed monic normalization at a nonzero original leading coefficient

The original descending coefficient list is multiplied by the actual
reciprocal of its first entry. A positive decoded squared numerator proves
the literal leading code is one. The numerical degree, list, scalar and
query remain internal. Horner linearity and exact recovery are derived for
the actual programs, without an assumed polynomial identity. This finite
component does not decide the exact degree of a coefficient name or prove
the general nonmonic travel estimate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalMonicNormalization

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul qzero canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (reciprocal normNumerator)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def head (C : PTm n) : PTm n := entry C zero
def inverse (C : PTm n) : PTm n := reciprocal (head C)
def normalized (C : PTm n) : PTm n := scaled C (inverse C)

ipra_subst head
ipra_subst inverse
ipra_subst normalized

theorem normalized_length (C : PTm n) : Γ ⊢[PRAAx] length (normalized C) ≐ length C :=
  GaussianRationalCoefficientScaling.scaled_length C (inverse C)

theorem normalized_lookup (C i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length C)) :
    Γ ⊢[PRAAx] entry (normalized C) i ≐ qmul (inverse C) (entry C i) :=
  GaussianRationalCoefficientScaling.scaled_lookup C (inverse C) i hi

theorem normalized_canonical (C : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (normalized C) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (normalized C))) :: Γ.map Fm.shift
  have originalRange : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (normalized C))) := Prf.hyp0
  have inputRange : Δ ⊢[PRAAx] lt (var 0) (length (normalized (Syn.shift C))) := by
    simpa only [Syn.shift,subst_normalized] using originalRange
  have range : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift C)) :=
    lt_congr (.eqRefl _) (normalized_length _) inputRange
  simpa only [Δ,Syn.shift,subst_normalized,normalized,
    GaussianRationalCoefficientScaling.subst_scaled,subst_inverse] using
    GaussianRationalCoefficientScaling.scaled_entry_canonical (Syn.shift C) (inverse (Syn.shift C)) (var 0) range

theorem head_times_inverse (C : PTm n) (hHead : Γ ⊢[PRAAx] le one (normNumerator (head C))) :
    Γ ⊢[PRAAx] qmul (head C) (inverse C) ≐ qone := GaussianRationalReciprocal.reciprocal_identity _ hHead

theorem normalized_leading (C : PTm n) (hLen : Γ ⊢[PRAAx] le one (length C))
    (hHead : Γ ⊢[PRAAx] le one (normNumerator (head C))) :
    Γ ⊢[PRAAx] entry (normalized C) zero ≐ qone :=
  (normalized_lookup C zero hLen).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (head_times_inverse C hHead))

theorem normalized_evaluation (C z : PTm n) : Γ ⊢[PRAAx]
    evaluate (normalized C) z ≐ qmul (inverse C) (evaluate C z) :=
  GaussianRationalCoefficientScaling.evaluation_linearity C (inverse C) z

/-- Multiplying the actual normalized output by the original first
coefficient recovers the original evaluation as a literal canonical code. -/
theorem recover_evaluation (C z : PTm n)
    (hHead : Γ ⊢[PRAAx] le one (normNumerator (head C))) : Γ ⊢[PRAAx]
    qmul (head C) (evaluate (normalized C) z) ≐ evaluate C z :=
  (qmul_congr (.eqRefl _) (normalized_evaluation C z)).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (head_times_inverse C hHead) (.eqRefl _)).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _)))))

theorem zero_iff (C z : PTm n) (hHead : Γ ⊢[PRAAx] le one (normNumerator (head C))) : Γ ⊢[PRAAx]
    Fm.iff (evaluate (normalized C) z ≐ qzero) (evaluate C z ≐ qzero) := by
  refine .andI (.impI ?_) (.impI ?_)
  · exact (recover_evaluation C z hHead.wk).eqSymm.eqTrans
      ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))
  · exact (normalized_evaluation C z).eqTrans
      ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _))

def normalizedF : PR 1 := PTm.toPR (normalized (var 0))
theorem program_at (C : PTm n) : Γ ⊢[PRAAx] ap1 normalizedF C ≐ normalized C := by
  simpa [normalizedF,ap1] using toPR_eq (Γ := Γ) (normalized (var 0) : PTm 1) ![C]

theorem monic_normalization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (length (var 0)) ⟶ le one (normNumerator (head (var 0))) ⟶
      (length (normalized (var 0)) ≐ length (var 0) ⋏ entry (normalized (var 0)) zero ≐ qone)) :=
  closeUniv 1 (.impI (.impI (.andI (normalized_length _) (normalized_leading _ Prf.hyp1 Prf.hyp0))))

theorem monic_normalization_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((ap1 normalizedF (var 0) ≐ normalized (var 0)) ⋏ canonicalCoefficients (normalized (var 0))) :=
  closeUniv 1 (.andI (program_at _) (normalized_canonical _))

theorem monic_normalization_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (evaluate (normalized (var 0)) (var 1) ≐ qmul (inverse (var 0)) (evaluate (var 0) (var 1))) :=
  closeUniv 2 (normalized_evaluation _ _)

theorem monic_normalization_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (normNumerator (head (var 0))) ⟶
      qmul (head (var 0)) (evaluate (normalized (var 0)) (var 1)) ≐ evaluate (var 0) (var 1)) :=
  closeUniv 2 (.impI (recover_evaluation _ _ Prf.hyp0))

theorem monic_normalization_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (normNumerator (head (var 0))) ⟶
      Fm.iff (evaluate (normalized (var 0)) (var 1) ≐ qzero) (evaluate (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (.impI (zero_iff _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalMonicNormalization
