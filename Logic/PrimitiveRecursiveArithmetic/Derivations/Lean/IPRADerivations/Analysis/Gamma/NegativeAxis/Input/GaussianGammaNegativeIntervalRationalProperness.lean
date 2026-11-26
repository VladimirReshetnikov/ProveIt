import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsoluteProperness
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalNamedInput
import IPRADerivations.Analysis.Optimization.Convexity.RationalMultiplicativeConvexity

/-!
# Rational input properness for negative Gamma and the critical point

Equal fractions have equal common-denominator codes for the original
negative-interval log magnitude and signed Gamma. The decoder applied to a
critical-point observation returns another exact encoding of that fraction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalRationalProperness

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaHalfSqrtBrackets (fraction_first_represents)
open GaussianGammaInputProperness (code_data_cross)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalGrid (denominator)
open GaussianGammaNegativeCriticalLocation (fractionLocationF fraction_location_at lower lower_guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData signed_gamma_source)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData name_regular)
open GaussianGammaNegativeIntervalLogAbsoluteProperness (log_absolute_rescale signed_rescale)
open GaussianGammaNegativeIntervalNamedInput (frozen_guard root_real_at root_sample root_source sampleNumerator sampleDenominator)
open GaussianGammaNegativeIntervalRescale (guard_rescale)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem through_common_encodings (f : PR 2) (x y u v : PTm n)
    (hu : Γ ⊢[PRAAx] pointCN f u) (hv : Γ ⊢[PRAAx] pointCN f v) (eq : Γ ⊢[PRAAx] u ≐ v)
    (left : Γ ⊢[PRAAx] crossEquivalent f f u x) (right : Γ ⊢[PRAAx] crossEquivalent f f v y) :
    Γ ⊢[PRAAx] crossEquivalent f f x y :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ (code_data_cross f u v hu hv eq) right)

theorem log_cross (a b c d N : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (eq : Γ ⊢[PRAAx] d*a ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (nameData a b N) (nameData c d N) := by
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hd := le_trans hc.andE₁ (le_of_lt hc.andE₂)
  have dataEq : Γ ⊢[PRAAx] nameData (d*a) (d*b) N ≐ nameData (b*c) (b*d) N := by
    simpa only [GaussianGammaNegativeIntervalLogAbsolute.subst_nameData, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (nameData (var 0) (var 1) (var 2) : PTm 3) (σ := ![d*a,d*b,N]) (σ' := ![b*c,b*d,N])
        (fun i => by fin_cases i; exact eq; exact mul_comm d b; exact .eqRefl N)
  exact through_common_encodings nameF _ _ _ _
    (name_regular _ _ N (guard_rescale a b d ha hd)) (name_regular _ _ N (guard_rescale c d b hc hb)) dataEq
    (log_absolute_rescale a b d N ha hd) (log_absolute_rescale c d b N hc hb)

theorem signed_cross (a b c d N : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c d)
    (eq : Γ ⊢[PRAAx] d*a ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent signedF signedF (signedData a b N) (signedData c d N) := by
  have hb := le_trans ha.andE₁ (le_of_lt ha.andE₂)
  have hd := le_trans hc.andE₁ (le_of_lt hc.andE₂)
  have dataEq : Γ ⊢[PRAAx] signedData (d*a) (d*b) N ≐ signedData (b*c) (b*d) N := by
    simpa only [GaussianGammaNegativeIntervalGammaSign.subst_signedData, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      Prf.eqCongr (signedData (var 0) (var 1) (var 2) : PTm 3) (σ := ![d*a,d*b,N]) (σ' := ![b*c,b*d,N])
        (fun i => by fin_cases i; exact eq; exact mul_comm d b; exact .eqRefl N)
  exact through_common_encodings signedF _ _ _ _
    (signed_gamma_source _ _ N (guard_rescale a b d ha hd)).andE₁
    (signed_gamma_source _ _ N (guard_rescale c d b hc hb)).andE₁ dataEq
    (signed_rescale a b d N ha hd) (signed_rescale c d b N hc hb)

theorem fraction_cross_products (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (eq : Γ ⊢[PRAAx] fraction a b ≐ fraction c d) : Γ ⊢[PRAAx] d*a ≐ b*c := by
  let q := fstT (fraction a b)
  have right : Γ ⊢[PRAAx] RationalArithmetic.represents q (ZT.ofNat c) d :=
    GaussianRationalHorner.scalar_congr (congrFst eq).eqSymm (.eqRefl _) (.eqRefl _) (fraction_first_represents c d hd)
  exact (mul_comm d a).eqTrans
    ((RationalMultiplicativeConvexity.natural_representation_cross q a b c d (fraction_first_represents a b hb) right).eqTrans
      (mul_comm c b))

theorem root_fraction (k N : PTm n) : Γ ⊢[PRAAx]
    fraction (sampleNumerator fractionLocationF k N) (sampleDenominator fractionLocationF k N) ≐ fraction (lower k N) (denominator k N) :=
  (GaussianUnitIntervalInputDecoding.fraction_recode (ap2 fractionLocationF k N) (mesh N) (root_sample k N)).eqTrans
    ((GaussianExponentialReference.recode_fixed _ (root_real_at k N).andE₁).eqTrans (fraction_location_at k N))

theorem root_guard (k N : PTm n) : Γ ⊢[PRAAx]
    guard (sampleNumerator fractionLocationF k N) (sampleDenominator fractionLocationF k N) :=
  frozen_guard fractionLocationF k N (mesh N) (root_source N)

theorem root_cross_products (k N : PTm n) : Γ ⊢[PRAAx]
    denominator k N*sampleNumerator fractionLocationF k N ≐ sampleDenominator fractionLocationF k N*lower k N :=
  fraction_cross_products _ _ _ _ (le_trans (root_guard (Γ := Γ) k N).andE₁ (le_of_lt (root_guard k N).andE₂))
    (GaussianGammaNegativeCriticalLocation.denominator_positive k N) (root_fraction k N)

theorem root_log_cross (k N : PTm n) : Γ ⊢[PRAAx] crossEquivalent nameF nameF
    (nameData (sampleNumerator fractionLocationF k N) (sampleDenominator fractionLocationF k N) N)
    (nameData (lower k N) (denominator k N) N) :=
  log_cross _ _ _ _ N (root_guard k N) (lower_guard k N) (root_cross_products k N)

theorem root_signed_cross (k N : PTm n) : Γ ⊢[PRAAx] crossEquivalent signedF signedF
    (signedData (sampleNumerator fractionLocationF k N) (sampleDenominator fractionLocationF k N) N)
    (signedData (lower k N) (denominator k N) N) :=
  signed_cross _ _ _ _ N (root_guard k N) (lower_guard k N) (root_cross_products k N)

theorem actual_original_negative_interval_rational_properness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((guard (var 0) (var 1) ⋏ (guard (var 2) (var 3) ⋏ (var 3*var 0 ≐ var 1*var 2))) ⟶
      (crossEquivalent nameF nameF (nameData (var 0) (var 1) (var 4)) (nameData (var 2) (var 3) (var 4)) ⋏
        crossEquivalent signedF signedF (signedData (var 0) (var 1) (var 4)) (signedData (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.andI
    (log_cross _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (signed_cross _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

theorem actual_original_negative_interval_root_freeze_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent nameF nameF
      (nameData (sampleNumerator fractionLocationF (var 0) (var 1)) (sampleDenominator fractionLocationF (var 0) (var 1)) (var 1))
      (nameData (lower (var 0) (var 1)) (denominator (var 0) (var 1)) (var 1)) ⋏
    crossEquivalent signedF signedF
      (signedData (sampleNumerator fractionLocationF (var 0) (var 1)) (sampleDenominator fractionLocationF (var 0) (var 1)) (var 1))
      (signedData (lower (var 0) (var 1)) (denominator (var 0) (var 1)) (var 1))) :=
  closeUniv 2 (.andI (root_log_cross _ _) (root_signed_cross _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalRationalProperness
