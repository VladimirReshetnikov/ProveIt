import GowersSzemeredi.Proofs13CompleteRowExtraction
import GowersSzemeredi.Proofs07IndexedPartition

/-! Stage 13.7 retaining the selected column's positive integer step ratio
and span in the Stage 13.6 progression. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- At the affine large scale, row extraction preserves the integer span
needed for short-parent localization and the common-step square construction. -/
theorem lemma_13_7_with_step_span {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hI : (criticalHeights S D E).Nonempty)
    (hlarge : 8 ≤ (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G ∧
      ∃ t : Nat, 0 < t ∧ G.S.step = (t : ZMod N) * F.R.step ∧
        t * (G.S.length - 1) < F.R.length := by
  classical
  have hR := stage136_progression_nonempty S D E F hF
  have hRcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hRlen : 0 < F.R.length := by simpa only [hRcard] using hR.card_pos
  have hY := hF.2.2.2.2.1
  obtain ⟨y, hy₁, hy₂⟩ := stage136_exists_base_row S D E F hF
  have hdense : (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length ≤
      (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card := by
    have h := stage137_base_row_density S.A F.R.carrier (criticalHeights S D E)
      F.Y y hI (fun h hh ↦ (hY h hh).1)
      (δ := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224)
      (by simpa only [hRcard] using hy₁)
    simpa only [hRcard] using h
  let delta : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  let A := F.R.carrier.filter fun x ↦ (x, y) ∈ S.A
  have hα := S.alpha_pos
  have hδ : 0 < delta := mul_pos (zpow_pos (by norm_num) _) (pow_pos hα _)
  have hδone : delta ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(43 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  obtain ⟨q, P, hP, hcell, t, ht, hspan⟩ := corollary_7_11_universal_modular_with_step_span
    N F.R A delta hF.2.2.1 hRlen hδ hδone (Finset.filter_subset _ _) hdense
    (by simpa only [delta, stage137_partition_exponent] using hlarge)
  obtain ⟨i, hi₁, hi₂⟩ := exists_stage137_partition_cell_two_bounds
    F.R.carrier (criticalHeights S D E) (fun i ↦ (P i).carrier) F.Y y hR hP
    (b₁ := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * (criticalHeights S D E).card)
    (b₂ := (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256 * E.Q.length)
    (by simpa only [hRcard, mul_assoc, mul_left_comm, mul_comm] using hy₁)
    (by simpa only [hRcard] using hy₂)
  obtain ⟨hstep, hproper, hlength, hlinear⟩ := hcell i
  have hbase : LinearOn ((P i).carrier.filter fun x ↦ (x, y) ∈ S.A)
      (fun x ↦ S.phi (x, y)) := by
    obtain ⟨a, b, hab⟩ := hlinear (fun x ↦ S.phi (x, y))
      (section13_base_row_freiman S F.R.carrier y)
    refine ⟨a, b, fun x hx => ?_⟩
    obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
    exact hab x (Finset.mem_filter.mpr
      ⟨hxP, Finset.mem_filter.mpr ⟨hP.cell_subset i hxP, hxA⟩⟩)
  have hcard : (P i).carrier.card = (P i).length := hproper
  let B := stage137UpperEndpoints (P i).carrier (criticalHeights S D E) F.Y y
  refine ⟨⟨y, P i, B⟩, ⟨?_, ?_⟩, t, ht, (hspan i).1, (hspan i).2⟩
  · refine ⟨hstep, hproper, hP.cell_subset i, ?_, Finset.filter_subset _ _, ?_, ?_, ?_⟩
    · simpa only [delta, stage137_partition_exponent] using hlength
    · simpa only [hcard, mul_assoc, mul_left_comm, mul_comm] using hi₁
    · simpa only [hcard] using hi₂
    · exact stage137UpperEndpoints_rows_linear S.A S.phi F.R.carrier (P i).carrier
        (criticalHeights S D E) F.Y y (hP.cell_subset i)
        (fun h hh ↦ (hY h hh).1) hbase (fun h hh ↦ (hY h hh).2.2)
  · exact stage137UpperEndpoints_subset_domain S.A (P i).carrier
      (criticalHeights S D E) F.Y y (fun h hh ↦ (hY h hh).1)

end LeanProofs.GowersSzemeredi
