import Surreal.HahnSeries.PredicateReconstruction
import Surreal.HahnSeries.NumberFieldExistentialGraph

/-!
# Internal coefficient reconstruction over number-field coefficients

The extension following `odg:def:cor:internal`, using the one-witness ideal
formula of `odg:def:rem:numberfieldideal`. A fixed numeral replaces the
original numeral two. No square root is a formula parameter.
-/

namespace Surreal.HahnSeries
open _root_.HahnSeries FirstOrder FirstOrder.Language
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Field L]
variable (o : Subring K) (j : K →+* L)
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (j.comp o.subtype)
local notation "ι" => coefficientRestrictedHahnInclusion (Γ := Γ) (j.comp o.subtype)
local instance numberFieldReconstructionNativeStructure : FirstOrder.Ring.CompatibleRing A :=
  FirstOrder.Ring.compatibleRingOfRing A

section Quadratic
variable (δ : ℕ) (hn : ¬IsSquare (δ : K)) (r : L) (hr : r ^ 2 = (δ : L))
local notation "φ" => TailoredExistentialGraphFormulas.ideal δ
include δ hn r hr

/-- The substituted ideal formula reconstructs the entire support ring on valid fraction pairs. -/
theorem numberFieldRestricted_reconstruction_mult_iff (a : Fin 2 → A) :
    (IdealReconstructionFormulas.multFormula φ).Realize a ↔
      a 1 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L :=
  native_reconstruction_mult_iff (j.comp o.subtype) φ
    (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr) a

/-- The native formula recovers the actual embedded coefficient field, including zero. -/
theorem numberFieldRestricted_reconstruction_coeff_iff (a : Fin 2 → A) :
    (IdealReconstructionFormulas.coeffFormula φ).Realize a ↔
      a 1 ≠ 0 ∧ ∃ c : L, ι (a 0) / ι (a 1) = C c :=
  native_reconstruction_coeff_iff (j.comp o.subtype) φ
    (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr) a

/-- The four-coordinate native formula recovers the coefficient map on the full support ring. -/
theorem numberFieldRestricted_reconstruction_graph_iff (a : Fin 4 → A) :
    (IdealReconstructionFormulas.graphFormula φ).Realize a ↔ a 1 ≠ 0 ∧ a 3 ≠ 0 ∧
      ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L ∧
      ι (a 2) / ι (a 3) = C ((ι (a 0) / ι (a 1)).coeff 0) :=
  native_reconstruction_graph_iff (j.comp o.subtype) φ
    (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr) a

/-- All three sets of fraction representatives are parameter-free native definable sets. -/
theorem numberFieldRestricted_reconstruction_definable :
    (∅ : Set A).Definable Language.ring
      {a : Fin 2 → A | a 1 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L} ∧
    (∅ : Set A).Definable Language.ring
      {a : Fin 2 → A | a 1 ≠ 0 ∧ ∃ c : L, ι (a 0) / ι (a 1) = C c} ∧
    (∅ : Set A).Definable Language.ring
      {a : Fin 4 → A | a 1 ≠ 0 ∧ a 3 ≠ 0 ∧
        ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L ∧
        ι (a 2) / ι (a 3) = C ((ι (a 0) / ι (a 1)).coeff 0)} :=
  ⟨reconstruction_support_definable (j.comp o.subtype) φ
      (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr),
    reconstruction_coefficients_definable (j.comp o.subtype) φ
      (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr),
    reconstruction_graph_definable (j.comp o.subtype) φ
      (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr)⟩

/-- The reconstructed field contains every ambient coefficient when the exponent group is nontrivial. -/
theorem numberFieldRestricted_reconstruction_covers_coefficients [Nontrivial Γ] (c : L) :
    ∃ a b : A, ι a / ι b = C c ∧
      (IdealReconstructionFormulas.coeffFormula φ).Realize ![a, b] :=
  native_reconstruction_covers_coefficients (j.comp o.subtype) φ
    (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr) c

end Quadratic

/-- The detector root hypothesis supplies a single numeral for all three native formulas. -/
theorem numberFieldRestricted_reconstruction_of_detector_root [NumberField K]
    (r : L) (hr : TailoredIntersectivePolynomial.value
      (NumberFieldTailoredGuard.pair K).p (NumberFieldTailoredGuard.pair K).q r = 0) :
    ∃ δ : ℕ, ¬IsSquare (δ : K) ∧
      (∀ a : Fin 2 → A,
        (IdealReconstructionFormulas.multFormula (TailoredExistentialGraphFormulas.ideal δ)).Realize a ↔
          a 1 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L) ∧
      (∀ a : Fin 2 → A,
        (IdealReconstructionFormulas.coeffFormula (TailoredExistentialGraphFormulas.ideal δ)).Realize a ↔
          a 1 ≠ 0 ∧ ∃ c : L, ι (a 0) / ι (a 1) = C c) ∧
      ∀ a : Fin 4 → A,
        (IdealReconstructionFormulas.graphFormula (TailoredExistentialGraphFormulas.ideal δ)).Realize a ↔
          a 1 ≠ 0 ∧ a 3 ≠ 0 ∧ ι (a 0) / ι (a 1) ∈ nonpositiveSupportSubring Γ L ∧
          ι (a 2) / ι (a 3) = C ((ι (a 0) / ι (a 1)).coeff 0) := by
  obtain ⟨δ, _, hn, hd⟩ := NumberFieldTailoredGuard.exists_nonsquare_radicand_of_root K r hr
  exact ⟨δ, hn, numberFieldRestricted_reconstruction_mult_iff o j δ hn r hd,
    numberFieldRestricted_reconstruction_coeff_iff o j δ hn r hd,
    numberFieldRestricted_reconstruction_graph_iff o j δ hn r hd⟩

end
end Surreal.HahnSeries
