import Mathlib

namespace OAI

section

section BSGCast

namespace NNRat
open scoped _root_.NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat

end BSGCast

section BSGDensity

namespace Finset
open scoped _root_.Finset
variable {K α β : Type*} [DivisionRing K] [CharZero K] [Fintype α] [Fintype β]
  {s t : Finset α} {a : α}

@[simp] lemma dens_product (s : Finset α) (t : Finset β) : (s ×ˢ t).dens = s.dens * t.dens := by
  simp [_root_.Finset.dens, mul_div_mul_comm]

variable [DecidableEq α]

lemma dens_union_eq_dens_add_dens : (s ∪ t).dens = s.dens + t.dens ↔ Disjoint s t := by
  rw [← _root_.Finset.dens_union_add_dens_inter]; simp [_root_.Finset.disjoint_iff_inter_eq_empty]

@[grind =]
lemma dens_sdiff_of_subset (h : s ⊆ t) : (t \ s).dens = t.dens - s.dens := by
  suffices (t \ s).dens = (t \ s ∪ s).dens - s.dens by rwa [_root_.Finset.sdiff_union_of_subset h] at this
  rw [_root_.Finset.dens_union_of_disjoint _root_.Finset.sdiff_disjoint, add_tsub_cancel_right]

lemma cast_dens_inter : ((s ∩ t).dens : K) = s.dens + t.dens - (s ∪ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact _root_.Finset.dens_inter_add_dens_union ..

lemma cast_dens_union : ((s ∪ t).dens : K) = s.dens + t.dens - (s ∩ t).dens := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact _root_.Finset.dens_union_add_dens_inter ..

lemma cast_dens_sdiff (h : s ⊆ t) : ((t \ s).dens : K) = t.dens - s.dens := by
  rw [dens_sdiff_of_subset h, NNRat.cast_sub (_root_.Finset.dens_mono h)]

end Finset

end BSGDensity

end

end OAI
