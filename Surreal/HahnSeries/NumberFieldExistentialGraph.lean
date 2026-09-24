import Surreal.Algebra.TailoredExistentialGraphFormulas
import Surreal.HahnSeries.NumberFieldQuadraticIdeal
import Surreal.HahnSeries.NumberFieldDetectorFormulas

/-!
# Existential number-field ideals and constant-term graphs

Proves the positive assertions of `odg:def:rem:numberfieldideal` in the full
coefficient pullback. One natural numeral supplies the quadratic equation;
its square root is used only in the proof, never as a formula parameter.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [Field L]
variable (o : Subring K) (j : K →+* L)
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (j.comp o.subtype)
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) (j.comp o.subtype)
local notation "ct" => coefficientRestrictedRetraction (Γ := Γ) (j.comp o.subtype)
  (j.injective.comp Subtype.val_injective)
local notation "ι" => coefficientRestrictedConstants (Γ := Γ) (j.comp o.subtype)

local instance numberFieldExistentialNativeStructure : FirstOrder.Ring.CompatibleRing A :=
  FirstOrder.Ring.compatibleRingOfRing A

/-- The native one-witness formula defines the purely infinite ideal. -/
theorem numberFieldRestricted_native_quadratic_ideal_iff (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) (a : A) :
    (TailoredExistentialGraphFormulas.ideal δ).Realize (fun _ => a) ↔ a ∈ I :=
  (TailoredExistentialGraphFormulas.realize_ideal δ _).trans
    (numberFieldRestricted_purelyInfinite_iff_quadratic o j δ hn r hr a).symm

/-- The quadratic equation gives a parameter-free native definition of the ideal. -/
theorem numberFieldRestricted_quadratic_ideal_definable (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) : (∅ : Set A).Definable₁ Language.ring (I : Set A) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨TailoredExistentialGraphFormulas.ideal δ, ?_⟩
  ext a
  have ha : (fun _ : Fin 1 => a 0) = a := funext fun i => congrArg a (Subsingleton.elim _ i)
  simpa only [ha, Set.mem_setOf_eq, SetLike.mem_coe] using
    (numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hr (a 0)).symm

variable [NumberField K] [CharZero L]
local notation "p₀" => NumberFieldTailoredGuard.PrimePair.p (NumberFieldTailoredGuard.pair K)
local notation "q₀" => NumberFieldTailoredGuard.PrimePair.q (NumberFieldTailoredGuard.pair K)

/-- The chosen number-field guard plus a quadratic witness gives the exact retraction graph. -/
theorem numberFieldRestricted_quadratic_graph_iff (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) (x n : A) :
    (TailoredDiophantineConstants.Xi p₀ q₀ n ∧ ∃ y : A, (x - n) ^ 2 = (δ : A) * y ^ 2) ↔
      n = ι (ct x) := by
  apply TailoredConstantTermGraph.quadratic_graph_iff p₀ q₀ δ ct ι
    (CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := L))
      (j.comp o.subtype) (j.injective.comp Subtype.val_injective)
      nonpositiveConstants nonpositiveConstantCoeff_constants)
    (numberFieldRestricted_xi_iff o j)
  intro a
  exact (numberFieldRestricted_purelyInfinite_iff_quadratic o j δ hn r hr a).symm.trans
    (CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := L))
      (j.comp o.subtype) (j.injective.comp Subtype.val_injective) a).symm

/-- The literal six-existential-variable native formula defines the retraction graph. -/
theorem numberFieldRestricted_native_existential_graph_iff (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) (a : Fin 2 → A) :
    (TailoredExistentialGraphFormulas.graph p₀ q₀ δ).Realize a ↔ a 1 = ι (ct (a 0)) :=
  (TailoredExistentialGraphFormulas.realize_graph p₀ q₀ δ a).trans
    (numberFieldRestricted_quadratic_graph_iff o j δ hn r hr (a 0) (a 1))

/-- The native existential graph has exactly one output for each input. -/
theorem numberFieldRestricted_existential_graph_existsUnique (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) (x : A) :
    ∃! n : A, (TailoredExistentialGraphFormulas.graph p₀ q₀ δ).Realize ![x, n] :=
  ⟨ι (ct x), (numberFieldRestricted_native_existential_graph_iff o j δ hn r hr _).mpr rfl,
    fun _ hgraph => (numberFieldRestricted_native_existential_graph_iff o j δ hn r hr _).mp hgraph⟩

/-- The graph is parameter-free definable with the exhibited existential syntax. -/
theorem numberFieldRestricted_existential_graph_definable (δ : ℕ) (hn : ¬IsSquare (δ : K))
    (r : L) (hr : r ^ 2 = (δ : L)) :
    (∅ : Set A).Definable Language.ring {a : Fin 2 → A | a 1 = ι (ct (a 0))} := by
  apply Set.empty_definable_iff.mpr
  refine ⟨TailoredExistentialGraphFormulas.graph p₀ q₀ δ, ?_⟩
  ext a
  exact (numberFieldRestricted_native_existential_graph_iff o j δ hn r hr a).symm

/-- Under the detector's original root hypothesis a single fixed numeral supplies both existential definitions. -/
theorem numberFieldRestricted_existential_definitions_of_detector_root
    (r : L) (hr : TailoredIntersectivePolynomial.value p₀ q₀ r = 0) :
    ∃ δ : ℕ, ¬IsSquare (δ : K) ∧
      (∀ a : A, (TailoredExistentialGraphFormulas.ideal δ).Realize (fun _ => a) ↔ a ∈ I) ∧
      (∀ a : Fin 2 → A, (TailoredExistentialGraphFormulas.graph p₀ q₀ δ).Realize a ↔
        a 1 = ι (ct (a 0))) ∧
      ∀ a : A, (TailoredDetectorFormulas.detector p₀ q₀).Realize (fun _ => a) ↔ a ∉ I := by
  obtain ⟨δ, _, hn, hd⟩ := NumberFieldTailoredGuard.exists_nonsquare_radicand_of_root K r hr
  exact ⟨δ, hn, numberFieldRestricted_native_quadratic_ideal_iff o j δ hn r hd,
    numberFieldRestricted_native_existential_graph_iff o j δ hn r hd,
    numberFieldRestricted_native_detector_iff o j r hr⟩

end
end Surreal.HahnSeries
