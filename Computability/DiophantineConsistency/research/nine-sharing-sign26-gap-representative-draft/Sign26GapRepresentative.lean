import DiophantineConsistency.SharingSign26Squares
import Sign26OrderedRing

/-! SOURCE-ONLY: a natural gap representative from an explicit Nt equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26GapRepresentative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_gap (beta K x1 x2 x3 x4 x9 : V) (hbeta : 1 ≤ beta)
    (hNt : (ι K + (ι x9 + 1)) *
        ((ι beta * (ι x1 + 1) + 1) - (ι x2 + 1) - (ι x3 + 1)) =
      (ι x2 + 1) + ι x4 * (ι beta * (ι x1 + 1))) :
    ∃ gap : V, ι gap = (ι beta * (ι x1 + 1)) * (ι beta * (ι x1 + 1) + 1) +
      (ι x3 + 1) - (ι beta * (ι x1 + 1)) * (ι x2 + 1) := by
  have hb : (1 : DiffRing V) ≤ ι beta := by simpa only [map_one] using (ι_le_ι.mpr hbeta)
  have hx1 := ι_nonneg x1
  have hp : 0 ≤ (ι beta - 1) * ι x1 := mul_nonneg (sub_nonneg.mpr hb) hx1
  have ha : (1 : DiffRing V) ≤ ι beta * (ι x1 + 1) := by nlinarith
  have hK := ι_nonneg K
  have hx9 := ι_nonneg x9
  have hH : (1 : DiffRing V) ≤ ι K + (ι x9 + 1) := by linarith
  have hx2 := ι_nonneg x2
  have hx3 := ι_nonneg x3
  have hn : (1 : DiffRing V) ≤ ι x2 + 1 := by linarith
  have ht : (1 : DiffRing V) ≤ ι x3 + 1 := by linarith
  have hz := ι_nonneg x4
  have hg := Sign26OrderedRing.gap_nonneg (ι beta * (ι x1 + 1)) (ι K + (ι x9 + 1))
    (ι x2 + 1) (ι x3 + 1) (ι x4) ha hH hn ht hz hNt
  obtain ⟨gap, hgap⟩ := nonneg_iff.mp hg
  exact ⟨gap, hgap.symm⟩
end DiophantineConsistency.Sign26GapRepresentative
#print axioms DiophantineConsistency.Sign26GapRepresentative.exists_gap
