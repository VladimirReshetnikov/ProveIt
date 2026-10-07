import GowersSzemeredi.Proofs13ConstructedSquare
import GowersSzemeredi.Proofs13AllScalesStepSpan

/-! The numbered Section 13 chain retains the geometric outputs of its
constructions. This closes the contextual square corollary without assuming
a grid or a bounded step that has not been constructed. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Lemma 13.9 with both its quantitative data and the geometry of the
selected witness, supplied from the preceding numbered conclusions. -/
theorem lemma_13_9_holds : lemma_13_9 := by
  intro N _ S D E F G H h135 h136 h137 hstep137 h138 hRlength
  obtain ⟨a, ha, hstep, hspan⟩ := hstep137
  obtain ⟨J, h139, hgeom⟩ := lemma_13_9_all_scales_with_geometry
    S D E F G H h135 h136 h137 h138 hRlength a ha hstep hspan
  have hRne := stage136_progression_nonempty S D E F h136
  have hRcard : F.R.carrier.card = F.R.length := h136.2.2.1
  have hRpos : 0 < F.R.length := by simpa only [hRcard] using hRne.card_pos
  have hGpos : 0 < G.S.length := by
    have hpos : (0 : Real) < G.S.length :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hRpos) _).trans_le h137.1.2.2.2.1
    exact_mod_cast hpos
  exact ⟨J, h139, h137.1.2.1, hGpos,
    stage139_support_of_stage137_stage138 S D E F G H J h137 h138 h139, hgeom⟩

/-- The full square corollary for the witness actually constructed by
Lemma 13.9, including every scale and the printed square-root length. -/
theorem corollary_13_10_holds : corollary_13_10 := by
  intro N _ S E G H J h139 hgeometry
  obtain ⟨hS, hGpos, hsupport, hgeom⟩ := hgeometry
  obtain ⟨V, W, E', hVs, hsteps, hV, hW, hlength, hwidth, _, hbox, hmass, hbilinear⟩ :=
    corollary_13_10_of_construction_geometry S E G H J h139 hS hGpos hsupport hgeom
  exact ⟨V, W, E', hVs, hsteps, hV, hW, hlength, hwidth, hbox, hmass, hbilinear⟩

end LeanProofs.GowersSzemeredi
