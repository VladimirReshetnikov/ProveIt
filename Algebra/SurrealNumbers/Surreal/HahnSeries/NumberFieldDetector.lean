import Surreal.Algebra.TailoredConstantTermGraph
import Surreal.HahnSeries.NumberFieldArithmeticConstants
import Surreal.HahnSeries.IntersectiveIdealTest
import Surreal.HahnSeries.ConstantTermGraph

/-!
# Number-field detectors, ideal tests and constant-term graphs

The remaining clauses of `odg:def:thm:numberfield`, using the verified
prime pair for each number field. The ambient coefficient field must contain
a root of the tailored sextic. These conclusions concern the full coefficient
pullback, not arbitrary intermediate subrings.
-/

namespace Surreal.HahnSeries
open TailoredIntersectivePolynomial
noncomputable section

variable {Γ K L : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
    [Field K] [NumberField K] [Field L]
variable (o : Subring K) (j : K →+* L)

attribute [local instance] nonpositiveSupportAlgebra
local notation "p₀" => NumberFieldTailoredGuard.PrimePair.p (NumberFieldTailoredGuard.pair K)
local notation "q₀" => NumberFieldTailoredGuard.PrimePair.q (NumberFieldTailoredGuard.pair K)
local notation "A" => coefficientRestrictedSubring (Γ := Γ) (j.comp o.subtype)
local notation "I" => coefficientRestrictedPurelyInfiniteIdeal (Γ := Γ) (j.comp o.subtype)
local notation "ct" => coefficientRestrictedRetraction (Γ := Γ) (j.comp o.subtype)
  (j.injective.comp Subtype.val_injective)
local notation "ι" => coefficientRestrictedConstants (Γ := Γ) (j.comp o.subtype)

/-- The tailored two-witness equation detects exactly the nonzero constant coefficients. -/
theorem numberFieldRestricted_detector_iff (r : L) (hr : value p₀ q₀ r = 0) (a : A) :
    Detects p₀ q₀ a ↔ nonpositiveConstantCoeff a.val ≠ 0 := by
  apply pullback_detector_iff p₀ q₀ (nonpositiveConstantCoeffAlgHom (Γ := Γ) (K := L))
    (j.comp o.subtype) (j.injective.comp Subtype.val_injective) _
    (numberField_subring_modular_value (NumberFieldTailoredGuard.pair K).admissible o) r hr a
  intro b hb
  have he := congrArg o.subtype hb
  rw [map_value, map_zero] at he
  exact value_ne_zero p₀ q₀ (NumberFieldTailoredGuard.pair K).p_nonsquare
    (NumberFieldTailoredGuard.pair K).q_nonsquare (NumberFieldTailoredGuard.pair K).pq_nonsquare b he

/-- The same detector, expressed in the native coefficient-ring retraction. -/
theorem numberFieldRestricted_detector_retraction_iff (r : L) (hr : value p₀ q₀ r = 0) (a : A) :
    Detects p₀ q₀ a ↔ ct a ≠ 0 := by
  have hc : ct a = 0 ↔ nonpositiveConstantCoeff a.val = 0 :=
    CoefficientPullback.mem_ker_iff (nonpositiveConstantCoeff (Γ := Γ) (R := L)) (j.comp o.subtype)
      (j.injective.comp Subtype.val_injective) a
  exact (numberFieldRestricted_detector_iff o j r hr a).trans (not_congr hc).symm

/-- A full-pullback ideal contains a tailored value precisely when it escapes the purely infinite ideal. -/
theorem numberFieldRestricted_ideal_contains_value_iff (r : L) (hr : value p₀ q₀ r = 0)
    (J : Ideal A) : (∃ t : A, value p₀ q₀ t ∈ J) ↔ ¬J ≤ I :=
  exists_value_mem_iff p₀ q₀ I (numberFieldRestricted_detector_iff o j r hr) J

/-- All native ideal quotients, including the zero ring, satisfy the exact root-free criterion. -/
theorem numberFieldRestricted_quotient_no_root_iff (r : L) (hr : value p₀ q₀ r = 0)
    (J : Ideal A) : (∀ t : A ⧸ J, value p₀ q₀ t ≠ 0) ↔ J ≤ I :=
  quotient_no_root_iff p₀ q₀ I (numberFieldRestricted_detector_iff o j r hr) J

/-- The purely infinite ideal is the greatest ideal with a root-free quotient. -/
theorem numberFieldRestricted_greatest_root_free_ideal (r : L) (hr : value p₀ q₀ r = 0) :
    IsGreatest {J : Ideal A | ∀ t : A ⧸ J, value p₀ q₀ t ≠ 0} I :=
  greatest_root_free_ideal p₀ q₀ I (numberFieldRestricted_detector_iff o j r hr)

/-- The universal two-variable formula defines the purely infinite ideal. -/
theorem numberFieldRestricted_purelyInfinite_iff_universal (r : L) (hr : value p₀ q₀ r = 0)
    (a : A) : a ∈ I ↔ ∀ s t : A, a * s ≠ value p₀ q₀ t :=
  mem_iff_universal p₀ q₀ I (numberFieldRestricted_detector_iff o j r hr) a

/-- On a difference, the universal formula detects equality of constant coefficients. -/
theorem numberFieldRestricted_constant_eq_iff_universal (r : L) (hr : value p₀ q₀ r = 0)
    (a b : A) : nonpositiveConstantCoeff a.val = nonpositiveConstantCoeff b.val ↔
      ∀ s t : A, (a - b) * s ≠ value p₀ q₀ t :=
  constant_eq_iff_universal p₀ q₀ (nonpositiveConstantCoeff.comp (A).subtype)
    (numberFieldRestricted_detector_iff o j r hr) a b

variable [CharZero L]

/-- The tailored constant predicate on the full pullback agrees with its native section. -/
theorem numberFieldRestricted_xi_iff (a : A) :
    TailoredDiophantineConstants.Xi p₀ q₀ a ↔ a ∈ (ι).range :=
  numberField_intermediate_tailored_xi_iff (NumberFieldTailoredGuard.pair K).admissible
    (NumberFieldTailoredGuard.pair K).p_nonsquare (NumberFieldTailoredGuard.pair K).q_nonsquare
    (NumberFieldTailoredGuard.pair K).pq_nonsquare o j A
    (coefficientRestricted_constants_intersection (j.comp o.subtype)) a

/-- Combining the constant guard with the universal test gives the exact retraction graph. -/
theorem numberFieldRestricted_graph_iff (r : L) (hr : value p₀ q₀ r = 0) (x n : A) :
    TailoredConstantTermGraph.Graph p₀ q₀ x n ↔ n = ι (ct x) :=
  TailoredConstantTermGraph.graph_iff p₀ q₀ ct ι
    (CoefficientPullback.retraction_sectionMap (nonpositiveConstantCoeff (Γ := Γ) (R := L)) (j.comp o.subtype)
      (j.injective.comp Subtype.val_injective) nonpositiveConstants nonpositiveConstantCoeff_constants)
    (numberFieldRestricted_xi_iff o j) (numberFieldRestricted_detector_retraction_iff o j r hr) x n

/-- The first displayed prenex form has five existential and two universal variables. -/
theorem numberFieldRestricted_graph_exists_forall_iff (r : L) (hr : value p₀ q₀ r = 0) (x n : A) :
    (∃ u v w s t : A, ∀ a b : A,
      TailoredDiophantineConstants.System p₀ q₀ n u v w s t ∧ (x - n) * a ≠ value p₀ q₀ b) ↔
        n = ι (ct x) :=
  (TailoredConstantTermGraph.graph_iff_exists_forall p₀ q₀ x n).symm.trans
    (numberFieldRestricted_graph_iff o j r hr x n)

/-- The second displayed prenex form has the reverse quantifier order. -/
theorem numberFieldRestricted_graph_forall_exists_iff (r : L) (hr : value p₀ q₀ r = 0) (x n : A) :
    (∀ a b : A, ∃ u v w s t : A,
      TailoredDiophantineConstants.System p₀ q₀ n u v w s t ∧ (x - n) * a ≠ value p₀ q₀ b) ↔
        n = ι (ct x) :=
  (TailoredConstantTermGraph.graph_iff_forall_exists p₀ q₀ x n).symm.trans
    (numberFieldRestricted_graph_iff o j r hr x n)

/-- Each input has exactly one output under either equivalent graph definition. -/
theorem numberFieldRestricted_graph_existsUnique (r : L) (hr : value p₀ q₀ r = 0) (x : A) :
    ∃! n, TailoredConstantTermGraph.Graph p₀ q₀ x n :=
  ⟨_, (numberFieldRestricted_graph_iff o j r hr x _).mpr rfl,
    fun n hn => (numberFieldRestricted_graph_iff o j r hr x n).mp hn⟩

end
end Surreal.HahnSeries
