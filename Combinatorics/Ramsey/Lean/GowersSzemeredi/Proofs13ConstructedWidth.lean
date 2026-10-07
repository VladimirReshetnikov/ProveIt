import GowersSzemeredi.Proofs13ConstructedChain
import GowersSzemeredi.Proofs13CoefficientExtraction

/-! A direct composition of the strengthened numbered extraction statements,
with no additional affine scale or square-grid assumptions. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Once the column width needed for Lemma 13.8 is reached, the numbered
construction gives a square with the full composed power, minus one. -/
theorem section13_square_extraction_of_width {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N) (F : Stage136Data N)
    (h135 : IsStage135Data S D E) (h136 : IsStage136Data S D E F)
    (hRupper : F.R.length ≤ E.Q.length)
    (hwidth : (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤
      (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) :
    ∃ V W : ModAP N, ∃ B : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧ V.length = W.length ∧
      (F.R.length : Real) ^ (((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) *
        ((2 : Real) ^ (-(284 : Int)) * S.alpha ^ 1408) / 2) - 1 ≤ V.length ∧
      B ⊆ S.A ∧ B ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ B.card ∧
      BilinearOn B S.phi := by
  classical
  obtain ⟨G, hG, hspan⟩ := lemma_13_7_holds N S D E F h136
  obtain ⟨H, hH⟩ := lemma_13_8_holds N S D E F G hG (hwidth.trans hG.1.2.2.2.1)
  obtain ⟨J, hJ, hgeom⟩ := lemma_13_9_holds N S D E F G H h135 h136 hG hspan hH hRupper
  obtain ⟨V, W, B, hVs, hsteps, hV, hW, hlength, hsize, hBD, hbox, hmass, hbilinear⟩ :=
    corollary_13_10_of_construction_geometry S E G H J hJ
      hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2
  have hα := S.alpha_pos
  let f : Real := (2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448
  let g : Real := (2 : Real) ^ (-(284 : Int)) * S.alpha ^ 1408
  have hg : 0 < g := by dsimp [g]; positivity
  have hfirst : (F.R.length : Real) ^ (f * g) ≤ J.U.length := by
    rw [Real.rpow_mul (Nat.cast_nonneg _)]
    exact (Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      hG.1.2.2.2.1 hg.le).trans hJ.2.2.2.2.1
  have hsecond : (F.R.length : Real) ^ (f * g / 2) ≤
      (J.U.length : Real) ^ ((1 : Real) / 2) := by
    rw [div_eq_mul_inv, Real.rpow_mul (Nat.cast_nonneg _)]
    simpa only [one_div] using Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg F.R.length) (f * g))
      hfirst (by norm_num : (0 : Real) ≤ (2 : Real)⁻¹)
  refine ⟨V, W, B, hVs, hsteps, hV, hW, hlength, ?_, ?_, hbox, hmass, hbilinear⟩
  · change (F.R.length : Real) ^ (f * g / 2) - 1 ≤ V.length
    linarith only [hsecond, hsize]
  · intro z hz
    have hzD := hBD hz
    rw [hJ.2.2.2.2.2.1] at hzD
    have hzC := (Finset.mem_filter.mp hzD).1
    rw [hH.2.2.2.1] at hzC
    exact hG.2 (Finset.mem_filter.mp hzC).1

end LeanProofs.GowersSzemeredi
