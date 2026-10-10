import GowersSzemeredi.Proofs16DifferenceAnchorCounts

/-! Difference maps from selected pairs of tiny-core anchors. Their
quadruple defects are eight-column defects, on exactly the retained
endpoint domains. The maps keep both origin normalizations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def differenceAnchorSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (v : ZMod N → ZMod N) (a : ZMod N) : Finset (ZMod N) := T (v a+a) ∪ T (v a)

def differenceAnchorMap {N : Nat} (F : ZMod N → ZMod N → ZMod N)
    (v : ZMod N → ZMod N) (a y : ZMod N) : ZMod N := F (v a+a) y-F (v a) y

def differenceAnchorPairedTuple {N : Nat} (v : ZMod N → ZMod N) (a b c e : ZMod N) : PairedColumnTuple N :=
  ![(v a+a,v a),(v b,v b+b),(v c,v c+c),(v e+e,v e)]

theorem difference_anchor_index_zero {N : Nat} (F : ZMod N → ZMod N → ZMod N)
    (v : ZMod N → ZMod N) (y : ZMod N) : differenceAnchorMap F v 0 y = 0 := by
  simp [differenceAnchorMap]

/-- The local spectrum, Freiman property and vertical normalization are
inherited from the two actual selected anchors. -/
theorem difference_anchor_map_data {N d : Nat} [NeZero N]
    (C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (F : ZMod N → ZMod N → ZMod N) (v : ZMod N → ZMod N) (rho : Real)
    (hdata : ∀ x ∈ C, (T x).card ≤ d ∧ IsFreimanLinearOn (bohr (T x) rho) (F x) ∧ F x 0 = 0)
    {a : ZMod N} (hva : v a ∈ C) (hva' : v a+a ∈ C) :
    (differenceAnchorSpectrum T v a).card ≤ 2*d ∧
      IsFreimanLinearOn (bohr (differenceAnchorSpectrum T v a) rho) (differenceAnchorMap F v a) ∧
      differenceAnchorMap F v a 0 = 0 := by
  have h0 := hdata (v a) hva
  have h1 := hdata (v a+a) hva'
  refine ⟨(Finset.card_union_le _ _).trans (by have := h0.1; have := h1.1; omega), ?_, ?_⟩
  · intro y1 y2 y3 y4 h2 h3 h4 h5 he
    simp only [differenceAnchorSpectrum, bohr_union, Finset.mem_inter] at h2 h3 h4 h5
    have ea := h1.2.1 y1 y2 y3 y4 h2.1 h3.1 h4.1 h5.1 he
    have eb := h0.2.1 y1 y2 y3 y4 h2.2 h3.2 h4.2 h5.2 he
    dsimp only [differenceAnchorMap]
    linear_combination ea-eb
  · simp only [differenceAnchorMap, h1.2.2, h0.2.2, sub_self]

theorem difference_anchor_paired_index {N : Nat} (v : ZMod N → ZMod N) (a b c e : ZMod N) :
    pairedColumnIndex (differenceAnchorPairedTuple v a b c e) = a-b-c+e := by
  rw [pairedColumnIndex, Fin.sum_univ_four]
  change ((v a+a)-v a)+(v b-(v b+b))+(v c-(v c+c))+((v e+e)-v e) = a-b-c+e
  ring

theorem difference_anchor_paired_defect {N : Nat} (F : ZMod N → ZMod N → ZMod N)
    (v : ZMod N → ZMod N) (a b c e y : ZMod N) :
    pairedColumnDefect F (differenceAnchorPairedTuple v a b c e) y =
      columnQuadDefect (differenceAnchorMap F v) a b c e y := by
  rw [pairedColumnDefect, Fin.sum_univ_four]
  change (F (v a+a) y-F (v a) y)+(F (v b) y-F (v b+b) y)+
      (F (v c) y-F (v c+c) y)+(F (v e+e) y-F (v e) y) =
    (F (v a+a) y-F (v a) y)-(F (v b+b) y-F (v b) y)-
      (F (v c+c) y-F (v c) y)+(F (v e+e) y-F (v e) y)
  ring

/-- The difference-map common domain retains all eight anchor spectra. -/
theorem difference_anchor_domain_subset {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (v : ZMod N → ZMod N) (rho : Real) (a b c e : ZMod N) :
    columnQuadCommonDomain (differenceAnchorSpectrum T v) rho a b c e ⊆
      bohr (pairedColumnSpectrum T (differenceAnchorPairedTuple v a b c e)) rho := by
  intro y hy
  obtain ⟨_,ha,hb,hc,he⟩ := Finset.mem_filter.mp hy
  simp only [differenceAnchorSpectrum, bohr_union, Finset.mem_inter] at ha hb hc he
  apply (mem_paired_column_spectrum_bohr T _ rho y).mpr
  intro i
  fin_cases i
  · exact ha
  · exact ⟨hb.2,hb.1⟩
  · exact ⟨hc.2,hc.1⟩
  · exact he

/-- Eight-term compatibility in the tiny core gives every quadruple
relation for the final progression-indexed difference maps. -/
theorem difference_progression_quad_images {N J : Nat} [NeZero N]
    (P C : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (F : ZMod N → ZMod N → ZMod N) (v : ZMod N → ZMod N) (rho : Real)
    (hv : ∀ a ∈ P, v a ∈ C ∧ v a+a ∈ C)
    (h8 : ∀ q : PairedColumnTuple N, (∀ i, (q i).1 ∈ C ∧ (q i).2 ∈ C) → pairedColumnIndex q = 0 →
      PairedColumnImageRelation T F rho J q) :
    ∀ a b c e : ZMod N, a ∈ P → b ∈ P → c ∈ P → e ∈ P → a-b = c-e →
      ColumnQuadImageRelation (differenceAnchorSpectrum T v) (differenceAnchorMap F v) rho J a b c e := by
  intro a b c e ha hb hc he hadd
  have hq : ∀ i, (differenceAnchorPairedTuple v a b c e i).1 ∈ C ∧
      (differenceAnchorPairedTuple v a b c e i).2 ∈ C := by
    intro i
    fin_cases i
    · exact ⟨(hv a ha).2,(hv a ha).1⟩
    · exact hv b hb
    · exact hv c hc
    · exact ⟨(hv e he).2,(hv e he).1⟩
  have hidx : pairedColumnIndex (differenceAnchorPairedTuple v a b c e) = 0 := by
    rw [difference_anchor_paired_index]
    linear_combination hadd
  have hsrc := h8 _ hq hidx
  apply (image_card_le_of_eq_on_subset _ _ _ _ (difference_anchor_domain_subset T v rho a b c e) ?_).trans hsrc
  intro y _
  exact (difference_anchor_paired_defect F v a b c e y).symm

end LeanProofs.GowersSzemeredi
