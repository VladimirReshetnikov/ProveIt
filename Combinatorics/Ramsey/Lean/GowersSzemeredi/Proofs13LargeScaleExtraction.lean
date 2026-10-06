import GowersSzemeredi.Proofs07ModularPartition
import GowersSzemeredi.Proofs13PartitionSelection

/-!
# The large-scale case of Lemma 13.7

The corrected Stage 13.6 relative density is `2^-43 * alpha^224`. Its
Corollary 7.11 exponent is exactly `2^-100 * alpha^448`, the exponent demanded
by Stage 13.7. The ceiling partition supplies the full real-power length
bound at an explicit scale; the earlier averaging and row-linearity lemmas
then assemble the complete Stage 13.7 conclusion.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- The corrected density gives precisely the exponent in Stage 13.7. -/
theorem stage137_partition_exponent (alpha : Real) :
    cor711Exponent ((2 : Real) ^ (-(43 : Int)) * alpha ^ 224) 1 =
      (2 : Real) ^ (-(100 : Int)) * alpha ^ 448 := by
  unfold cor711Exponent
  norm_num [Real.rpow_neg, zpow_neg]
  ring

/-- Construct the missing affine partition of any sufficiently dense base
row under the explicit rounding-safe scale condition. -/
theorem stage137_affine_base_partition_large {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (F : Stage136Data N)
    (hproper : F.R.IsProper) (hlen : 0 < F.R.length)
    (hlarge : 4096 * Real.pi / ((2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224) ≤
      (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448))
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
  obtain ⟨M, P, hP, hcell⟩ := corollary_7_11_modular N F.R A
    (fun x ↦ S.phi (x, y)) δ hproper hlen hδ hδone
    (Finset.filter_subset _ _) hdense (section13_base_row_freiman S F.R.carrier y)
    (by simpa only [δ, stage137_partition_exponent] using hlarge)
  refine ⟨M, P, hP, ?_⟩
  intro j
  obtain ⟨hstep, hp, hl, a, b, hlin⟩ := hcell j
  refine ⟨hstep, hp, ?_, a, b, ?_⟩
  · simpa only [δ, stage137_partition_exponent] using hl
  · intro x hx
    obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
    exact hlin x (Finset.mem_filter.mpr
      ⟨hxP, Finset.mem_filter.mpr ⟨hP.cell_subset j hxP, hxA⟩⟩)

/-- Lemma 13.7 at a scale where the repaired Corollary 7.11 construction
applies. Primality and the numerical threshold remain explicit. -/
theorem lemma_13_7_large_scale {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hlarge : 4096 * Real.pi / ((2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224) ≤
      (F.R.length : Real) ^ ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448)) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  apply lemma_13_7_of_affine_base_partitions S D E F hF
  have hR := stage136_progression_nonempty S D E F hF
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hlen : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  exact stage137_affine_base_partition_large S F hF.2.2.1 hlen hlarge

end LeanProofs.GowersSzemeredi
