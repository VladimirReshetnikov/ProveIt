import GowersSzemeredi.Proofs13DenseRowPopulation

/-! The large-density rows share one global bilinear formula. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem section13_dense_row_coefficients_freiman_two {N : Nat} [Fact N.Prime]
    (hN : 5 ≤ N) (S : Section13Context N) (a c : ZMod N → ZMod N)
    (hrow : ∀ y ∈ section13DenseRows S.A, ∀ x ∈ horizontalSection S.A y,
      S.phi (x, y) = a y + c y * x) :
    FreimanHom 2 (section13DenseRows S.A) (fun y ↦ (a y, c y)) := by
  classical
  apply isAddFreimanHom_two.mpr
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro y1 hy1 y2 hy2 y3 hy3 y4 hy4 heq
  let ys : Fin 4 → ZMod N := ![y1, y2, y3, y4]
  let T : Fin 4 → Finset (ZMod N) := fun i ↦ horizontalSection S.A (ys i)
  have hT : ∀ i, 4 * N < 5 * (T i).card := by
    intro i
    fin_cases i
    · exact (Finset.mem_filter.mp hy1).2
    · exact (Finset.mem_filter.mp hy2).2
    · exact (Finset.mem_filter.mp hy3).2
    · exact (Finset.mem_filter.mp hy4).2
  obtain ⟨x1, x2, hne, hx1, hx2⟩ := four_large_domains_common_columns hN T hT
  have eval (x : ZMod N) (hx : ∀ i, x ∈ T i) :
      (a y1 + c y1 * x) + (a y2 + c y2 * x) =
        (a y3 + c y3 * x) + (a y4 + c y4 * x) := by
    have hx0 : x ∈ horizontalSection S.A y1 := by simpa only [T, ys, Matrix.cons_val_zero] using hx 0
    have hx1 : x ∈ horizontalSection S.A y2 := by simpa [T, ys] using hx 1
    have hx2 : x ∈ horizontalSection S.A y3 := by simpa [T, ys] using hx 2
    have hx3 : x ∈ horizontalSection S.A y4 := by simpa [T, ys] using hx 3
    have mem (y : ZMod N) (hy : x ∈ horizontalSection S.A y) : y ∈ verticalSection S.A x := by
      simpa only [horizontalSection, verticalSection, Finset.mem_filter,
        Finset.mem_univ, true_and] using hy
    have hf : FreimanHom 2 (verticalSection S.A x) (fun y ↦ S.phi (x, y)) :=
      IsAddFreimanHom.mono (by norm_num) (S.separately_freiman.1 x)
    have h := hf.add_eq_add (mem y1 hx0) (mem y2 hx1) (mem y3 hx2) (mem y4 hx3) heq
    rw [hrow y1 hy1 x hx0, hrow y2 hy2 x hx1, hrow y3 hy3 x hx2, hrow y4 hy4 x hx3] at h
    exact h
  have e1 := eval x1 hx1
  have e2 := eval x2 hx2
  have hc : c y1 + c y2 = c y3 + c y4 := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    linear_combination e1 - e2
  have ha : a y1 + a y2 = a y3 + a y4 := by
    linear_combination e1 - x1 * hc
  exact Prod.ext ha hc

/-- At density greater than14/15, all points in the dense-row piece agree
with one global bilinear polynomial. The discarded mass is quantified by
section13_dense_row_piece_mass. -/
theorem section13_dense_row_piece_bilinear {N : Nat} [Fact N.Prime]
    (hN : 5 ≤ N) (S : Section13Context N) (hα : 14 / 15 < S.alpha) :
    BilinearOn (section13DenseRowPiece S.A) S.phi := by
  classical
  have hex : ∀ y : ZMod N, ∃ a c : ZMod N,
      y ∈ section13DenseRows S.A → ∀ x ∈ horizontalSection S.A y,
        S.phi (x, y) = a + c * x := by
    intro y
    by_cases hy : y ∈ section13DenseRows S.A
    · obtain ⟨a, c, hrow⟩ := section13_dense_rows_affine S y hy
      exact ⟨a, c, fun _ ↦ hrow⟩
    · exact ⟨0, 0, fun h ↦ (hy h).elim⟩
  choose a c hrow using hex
  have hp := section13_dense_row_coefficients_freiman_two hN S a c hrow
  have ha : FreimanHom 2 (section13DenseRows S.A) a :=
    (AddHomClass.isAddFreimanHom (AddMonoidHom.fst (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hp
  have hc : FreimanHom 2 (section13DenseRows S.A) c :=
    (AddHomClass.isAddFreimanHom (AddMonoidHom.snd (ZMod N) (ZMod N))
      (Set.mapsTo_univ _ _)).comp hp
  have hdense := section13_dense_rows_large S hα
  obtain ⟨aa, ab, ha⟩ := dense_freiman_two_linear _ a ha hdense
  obtain ⟨ca, cb, hc⟩ := dense_freiman_two_linear _ c hc hdense
  let mu : Pair N → ZMod N := fun z ↦ ab + cb * z.1 + aa * z.2 + ca * z.1 * z.2
  refine ⟨mu, ⟨ab, cb, aa, ca, fun _ ↦ rfl⟩, ?_⟩
  intro z hz
  obtain ⟨hzA, hzGood⟩ := Finset.mem_filter.mp hz
  have hx : z.1 ∈ horizontalSection S.A z.2 := by
    simp only [horizontalSection, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hzA
  rw [hrow z.2 hzGood z.1 hx, ha z.2 hzGood, hc z.2 hzGood]
  dsimp only [mu]
  ring

end LeanProofs.GowersSzemeredi
