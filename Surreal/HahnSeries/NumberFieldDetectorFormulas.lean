import Surreal.HahnSeries.NumberFieldDetector
import Surreal.Algebra.TailoredDetectorFormulas

/-!
# Native definability of the number-field detector and retraction graph

The first-order syntax conclusions in `odg:def:thm:numberfield`. The two
prenex formulas define the same unique output, and the unary formulas
define the purely infinite ideal and its complement without parameters.
-/

namespace Surreal.HahnSeries
open FirstOrder FirstOrder.Language TailoredIntersectivePolynomial
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [NumberField K] [Field L]
variable (o : Subring K) (j : K →+* L)
local notation "p₀" => NumberFieldTailoredGuard.PrimePair.p (NumberFieldTailoredGuard.pair K)
local notation "q₀" => NumberFieldTailoredGuard.PrimePair.q (NumberFieldTailoredGuard.pair K)
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (j.comp o.subtype)
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) (j.comp o.subtype)
local notation "ct" => coefficientRestrictedRetraction (Γ := Γ) (j.comp o.subtype)
  (j.injective.comp Subtype.val_injective)
local notation "ι" => coefficientRestrictedConstants (Γ := Γ) (j.comp o.subtype)

local instance numberFieldDetectorNativeStructure : FirstOrder.Ring.CompatibleRing A :=
  FirstOrder.Ring.compatibleRingOfRing A

/-- The native existential detector defines exactly the complement of the purely infinite ideal. -/
theorem numberFieldRestricted_native_detector_iff (r : L) (hr : value p₀ q₀ r = 0) (a : A) :
    (TailoredDetectorFormulas.detector p₀ q₀).Realize (fun _ => a) ↔ a ∉ I :=
  (TailoredDetectorFormulas.realize_detector p₀ q₀ _).trans
    (numberFieldRestricted_detector_iff o j r hr a)

/-- The native universal formula defines the purely infinite ideal. -/
theorem numberFieldRestricted_native_ideal_iff (r : L) (hr : value p₀ q₀ r = 0) (a : A) :
    (TailoredDetectorFormulas.ideal p₀ q₀).Realize (fun _ => a) ↔ a ∈ I :=
  (TailoredDetectorFormulas.realize_ideal p₀ q₀ _).trans
    (numberFieldRestricted_purelyInfinite_iff_universal o j r hr a).symm

variable [CharZero L]

/-- The literal existential-universal syntax defines the embedded retraction graph. -/
theorem numberFieldRestricted_native_graphExistsForall_iff
    (r : L) (hr : value p₀ q₀ r = 0) (a : Fin 2 → A) :
    (TailoredDetectorFormulas.graphExistsForall p₀ q₀).Realize a ↔ a 1 = ι (ct (a 0)) :=
  (TailoredDetectorFormulas.realize_graphExistsForall p₀ q₀ a).trans
    (numberFieldRestricted_graph_iff o j r hr (a 0) (a 1))

/-- The literal universal-existential syntax defines the very same graph. -/
theorem numberFieldRestricted_native_graphForallExists_iff
    (r : L) (hr : value p₀ q₀ r = 0) (a : Fin 2 → A) :
    (TailoredDetectorFormulas.graphForallExists p₀ q₀).Realize a ↔ a 1 = ι (ct (a 0)) :=
  (TailoredDetectorFormulas.realize_graphForallExists p₀ q₀ a).trans
    (numberFieldRestricted_graph_iff o j r hr (a 0) (a 1))

omit [CharZero L] in
/-- The purely infinite ideal is parameter-free definable in Mathlib's native sense. -/
theorem numberFieldRestricted_ideal_definable (r : L) (hr : value p₀ q₀ r = 0) :
    (∅ : Set A).Definable₁ Language.ring (I : Set A) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨TailoredDetectorFormulas.ideal p₀ q₀, ?_⟩
  ext a
  have ha : (fun _ : Fin 1 => a 0) = a := funext fun i => congrArg a (Subsingleton.elim _ i)
  simpa only [ha, Set.mem_setOf_eq, SetLike.mem_coe] using (numberFieldRestricted_native_ideal_iff o j r hr (a 0)).symm

omit [CharZero L] in
/-- The complement also has a parameter-free native definition, with two existential witnesses. -/
theorem numberFieldRestricted_ideal_complement_definable (r : L) (hr : value p₀ q₀ r = 0) :
    (∅ : Set A).Definable₁ Language.ring ((I : Set A)ᶜ) := by
  apply Set.empty_definable_iff.mpr
  refine ⟨TailoredDetectorFormulas.detector p₀ q₀, ?_⟩
  ext a
  have ha : (fun _ : Fin 1 => a 0) = a := funext fun i => congrArg a (Subsingleton.elim _ i)
  simpa only [ha, Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe] using (numberFieldRestricted_native_detector_iff o j r hr (a 0)).symm

/-- The retraction graph is parameter-free definable as a native binary relation. -/
theorem numberFieldRestricted_graph_definable (r : L) (hr : value p₀ q₀ r = 0) :
    (∅ : Set A).Definable Language.ring {a : Fin 2 → A | a 1 = ι (ct (a 0))} := by
  apply Set.empty_definable_iff.mpr
  refine ⟨TailoredDetectorFormulas.graphExistsForall p₀ q₀, ?_⟩
  ext a
  exact (numberFieldRestricted_native_graphExistsForall_iff o j r hr a).symm

end
end Surreal.HahnSeries
