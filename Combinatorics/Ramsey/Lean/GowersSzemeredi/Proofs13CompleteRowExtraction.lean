import GowersSzemeredi.Proofs07NinePointLinearity
import GowersSzemeredi.Proofs13LargeScaleExtraction

/-! Complete the corrected prime-modulus Lemma 13.7, without any lower-scale
hypothesis. Both density lower bounds and original-domain containment are
retained, as is the exponent propagated from the corrected Stage 13.6. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Construct an affine partition of every sufficiently dense base row,
retaining the exact exponent and imposing no scale threshold. -/
theorem stage137_affine_base_partition {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (F : Stage136Data N)
    (hproper : F.R.IsProper) (hstep : F.R.step != 0) (hlen : 0 < F.R.length)
    (y : ZMod N)
    (hdense : (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224 * F.R.length ≤
      (F.R.carrier.filter fun x ↦ (x, y) ∈ S.A).card) :
    Stage137AffineBasePartition S F y := by
  classical
  let δ : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  let A := F.R.carrier.filter fun x ↦ (x, y) ∈ S.A
  have hα := S.alpha_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(43 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  obtain ⟨M, P, hP, hcell⟩ := corollary_7_11_all_scales_modular N F.R A
    (fun x ↦ S.phi (x, y)) δ hproper hstep hlen hδ hδone
    (Finset.filter_subset _ _) hdense (section13_base_row_freiman S F.R.carrier y)
  refine ⟨M, P, hP, ?_⟩
  intro j
  obtain ⟨hstep, hp, hl, a, b, hlin⟩ := hcell j
  refine ⟨hstep, hp, ?_, a, b, ?_⟩
  · simpa only [δ, stage137_partition_exponent] using hl
  · intro x hx
    obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
    exact hlin x (Finset.mem_filter.mpr
      ⟨hxP, Finset.mem_filter.mpr ⟨hP.cell_subset j hxP, hxA⟩⟩)


/-- The complete corrected Lemma 13.7 under the standing prime assumption. -/
theorem lemma_13_7_holds : lemma_13_7 := by
  intro N _ S D E F hF
  apply lemma_13_7_of_affine_base_partitions S D E F hF
  have hR := stage136_progression_nonempty S D E F hF
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hlen : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  exact stage137_affine_base_partition S F hF.2.2.1 hF.2.1 hlen

end LeanProofs.GowersSzemeredi
