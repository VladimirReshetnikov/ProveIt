import Surreal.Algebra.AdicCompletionTopology
import Surreal.Algebra.PadicResidueTopology
import Surreal.Foundations.OmnificSeparationTopology
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.DenseEmbedding

/-!
# The p-adic completion homeomorphism for actual omnific integers

The p-adic topological isomorphism in `odg:eq:profinite`. The algebraic
completion carries its inverse-limit topology of discrete ideal-power
quotients. Its ring equivalence with Mathlib's metric p-adic integers is a
homeomorphism. The canonical map has dense image, induces the omnific
p-adic topology, and is integer constant extraction followed by the usual
integer embedding under this homeomorphism.
-/

universe u
namespace Surreal.Foundations.SignSequence

open Topology

noncomputable section

/-- The existing p-adic ring isomorphism induces the standard inverse-limit topology. -/
theorem isInducing_omnificPadicCompletionEquiv (p : ℕ) [Fact p.Prime] :
    IsInducing (omnificPadicCompletionEquiv.{u} p) := by
  apply isInducing_iff_nhds.mpr
  intro x
  apply (AdicCompletionTopology.hasBasis_nhds (omnificPadicIdeal p) x).eq_of_same_basis
  apply ((PadicResidueTopology.hasBasis_nhds p (omnificPadicCompletionEquiv p x)).comap
    (omnificPadicCompletionEquiv p)).congr (fun _ => Iff.rfl)
  intro n _
  ext y
  change PadicInt.toZModPow n (omnificCompletionToPadic p y) =
    PadicInt.toZModPow n (omnificCompletionToPadic p x) ↔ _
  rw [toZModPow_omnificCompletionToPadic, toZModPow_omnificCompletionToPadic]
  exact (omnificPadicQuotientEquiv p n).injective.eq_iff

/-- The p-adic ring isomorphism is a homeomorphism for the inverse-limit and metric topologies. -/
def omnificPadicHomeomorph (p : ℕ) [Fact p.Prime] : OmnificPadicCompletion.{u} p ≃ₜ ℤ_[p] where
  toEquiv := (omnificPadicCompletionEquiv p).toEquiv
  continuous_toFun := (isInducing_omnificPadicCompletionEquiv p).continuous
  continuous_invFun := (isInducing_omnificPadicCompletionEquiv p).continuous_iff.mpr (by
    change Continuous (fun x => omnificPadicCompletionEquiv p
      ((omnificPadicCompletionEquiv p).symm x))
    simp only [RingEquiv.apply_symm_apply]
    exact continuous_id)

/-- The homeomorphism has precisely the earlier ring equivalence as its function. -/
@[simp] theorem omnificPadicHomeomorph_apply (p : ℕ) [Fact p.Prime]
    (x : OmnificPadicCompletion.{u} p) :
    omnificPadicHomeomorph p x = omnificPadicCompletionEquiv p x := rfl

/-- The topological completion map extracts the integer constant before embedding in p-adics. -/
theorem omnificPadicHomeomorph_of (p : ℕ) [Fact p.Prime] (x : OmnificInteger.{u}) :
    omnificPadicHomeomorph p (AdicCompletion.of (omnificPadicIdeal p) OmnificInteger x) =
      (omnificConstantCoeff x : ℤ_[p]) := omnificPadicCompletionEquiv_of p x

/-- The actual omnific p-adic completion is compact in the inverse-limit topology. -/
instance omnificPadicCompletionCompactSpace (p : ℕ) [Fact p.Prime] :
    CompactSpace (OmnificPadicCompletion.{u} p) := (omnificPadicHomeomorph p).symm.compactSpace

/-- The actual omnific integers have dense image in their p-adic completion. -/
theorem denseRange_omnificPadic_of (p : ℕ) :
    DenseRange (AdicCompletion.of (omnificPadicIdeal.{u} p) OmnificInteger) :=
  AdicCompletionTopology.denseRange_of _

/-- The canonical p-adic completion map induces exactly the omnific prime-adic topology. -/
theorem isInducing_omnificPadic_of (p : ℕ) :
    @IsInducing OmnificInteger.{u} (OmnificPadicCompletion p) (omnificPadicTopology p)
      inferInstance (AdicCompletion.of (omnificPadicIdeal p) OmnificInteger) :=
  AdicCompletionTopology.isInducing_of _

/-- The canonical p-adic completion map is continuous. -/
theorem continuous_omnificPadic_of (p : ℕ) :
    @Continuous OmnificInteger.{u} (OmnificPadicCompletion p) (omnificPadicTopology p)
      inferInstance (AdicCompletion.of (omnificPadicIdeal p) OmnificInteger) := by
  letI := omnificPadicTopology.{u} p
  exact (isInducing_omnificPadic_of p).continuous

/-- Density and the induced topology hold even though the canonical map has nonzero kernel. -/
theorem isDenseInducing_omnificPadic_of (p : ℕ) :
    @IsDenseInducing OmnificInteger.{u} (OmnificPadicCompletion p) (omnificPadicTopology p)
      inferInstance (AdicCompletion.of (omnificPadicIdeal p) OmnificInteger) := by
  letI := omnificPadicTopology.{u} p
  exact ⟨isInducing_omnificPadic_of p, denseRange_omnificPadic_of p⟩

/-- The ordinary integer ideal-adic topology used for separation is the p-adic subspace topology. -/
theorem isEmbedding_integerPadic_intCast (p : ℕ) [Fact p.Prime] :
    @IsEmbedding ℤ ℤ_[p] (integerPadicTopology p) inferInstance Int.cast := by
  letI := integerPadicTopology p
  exact ⟨PadicResidueTopology.isInducing_intCast p, Int.cast_injective⟩

end
end Surreal.Foundations.SignSequence
