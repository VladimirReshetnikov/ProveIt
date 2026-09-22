import Surreal.Foundations.SignSequenceRationals
import Surreal.HahnSeries.RealClosed
import Surreal.HahnSeries.AlgebraicallyClosed
import Surreal.Algebra.RealClosedReal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.DFinsupp.Small
import Mathlib.Logic.Small.Set
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Small divisible exponent workspaces in the actual sign field

The rational span of a small exponent set together with one is small,
nonzero and divisible. Small families of these sets admit a common such
enlargement. This implements the exponent-group construction in
`found:thm:workspace` without presupposing an infinite normal-form theorem.
The resulting abstract real and complex Hahn fields are closed and small;
their infinite embeddings into the actual carriers remain separate.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Adjoin the nonzero exponent one and close under rational linear combinations. -/
def workspaceExponents (s : Set SignSequence.{u}) : Submodule ℚ SignSequence.{u} :=
  Submodule.span ℚ (insert 1 s)

theorem subset_workspaceExponents (s : Set SignSequence.{u}) :
    s ⊆ workspaceExponents s :=
  fun _ hx => Submodule.subset_span (Set.mem_insert_of_mem _ hx)

theorem one_mem_workspaceExponents (s : Set SignSequence.{u}) :
    (1 : SignSequence.{u}) ∈ workspaceExponents s :=
  Submodule.subset_span (Set.mem_insert _ _)

/-- Finite rational combinations of a small set still form a small set. -/
instance small_workspaceExponents (s : Set SignSequence.{u}) [Small.{u} s] :
    Small.{u} (workspaceExponents s) := by
  rw [workspaceExponents, Finsupp.span_eq_range_linearCombination]
  exact small_of_surjective (LinearMap.surjective_rangeRestrict _)

instance nontrivial_workspaceExponents (s : Set SignSequence.{u}) :
    Nontrivial (workspaceExponents s) := by
  refine ⟨⟨0, ⟨1, one_mem_workspaceExponents s⟩, ?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h)

/-- Rational scalar division stays inside the generated exponent group. -/
instance divisible_workspaceExponents (s : Set SignSequence.{u}) :
    DivisibleBy (workspaceExponents s) ℕ where
  div a n := (n : ℚ)⁻¹ • a
  div_zero a := by simp
  div_cancel a hn := by
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

theorem workspaceExponents_mono {s t : Set SignSequence.{u}} (hst : s ⊆ t) :
    workspaceExponents s ≤ workspaceExponents t :=
  Submodule.span_mono (Set.insert_subset_insert hst)

/-- Enlargement is an actual additive inclusion of exponent groups. -/
def workspaceExponentInclusion {s t : Set SignSequence.{u}} (hst : s ⊆ t) :
    workspaceExponents s →+ workspaceExponents t :=
  (Submodule.inclusion (workspaceExponents_mono hst)).toAddMonoidHom

theorem workspaceExponentInclusion_strictMono {s t : Set SignSequence.{u}} (hst : s ⊆ t) :
    StrictMono (workspaceExponentInclusion hst) := fun _ _ h => h

/-- A small family of small exponent sets has a common small divisible enlargement. -/
theorem small_common_workspaceExponents {ι : Type v} [Small.{u} ι]
    (s : ι → Set SignSequence.{u}) [∀ i, Small.{u} (s i)] :
    Small.{u} (workspaceExponents (⋃ i, s i)) ∧
      ∀ i, workspaceExponents (s i) ≤ workspaceExponents (⋃ i, s i) :=
  ⟨inferInstance, fun i => workspaceExponents_mono (Set.subset_iUnion s i)⟩

/-- A single small exponent workspace cannot contain every surreal exponent. -/
theorem exists_not_mem_workspaceExponents (s : Set SignSequence.{u}) [Small.{u} s] :
    ∃ x : SignSequence.{u}, x ∉ workspaceExponents s := by
  by_contra h
  push Not at h
  have hs : Small.{u} SignSequence.{u} :=
    small_of_surjective (f := fun x : workspaceExponents s => x.val)
      (fun x => ⟨⟨x, h x⟩, rfl⟩)
  exact not_small hs

/-- Real Hahn series on these exponents, with their lexicographic order. -/
abbrev RealHahnWorkspace (s : Set SignSequence.{u}) :=
  Lex (_root_.HahnSeries (workspaceExponents s) ℝ)

/-- Complex Hahn series on these exponents. -/
abbrev ComplexHahnWorkspace (s : Set SignSequence.{u}) :=
  _root_.HahnSeries (workspaceExponents s) ℂ

instance small_realHahnWorkspace (s : Set SignSequence.{u}) [Small.{u} s] :
    Small.{u} (RealHahnWorkspace s) :=
  small_of_injective (f := fun x : RealHahnWorkspace s => (ofLex x).coeff)
    (fun _ _ h => congrArg toLex (_root_.HahnSeries.ext h))

instance small_complexHahnWorkspace (s : Set SignSequence.{u}) [Small.{u} s] :
    Small.{u} (ComplexHahnWorkspace s) :=
  small_of_injective (f := fun x : ComplexHahnWorkspace s => x.coeff)
    (fun _ _ h => _root_.HahnSeries.ext h)

/-- Closedness is supplied by the proved Hahn construction, not by an assumption. -/
theorem realHahnWorkspace_isRealClosed (s : Set SignSequence.{u}) :
    IsRealClosed (RealHahnWorkspace s) := inferInstance

theorem complexHahnWorkspace_isAlgClosed (s : Set SignSequence.{u}) :
    IsAlgClosed (ComplexHahnWorkspace s) := inferInstance

end

end Surreal.Foundations.SignSequence
