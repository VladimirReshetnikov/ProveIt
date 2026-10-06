import GowersSzemeredi.Proofs07ShortLinearity
import GowersSzemeredi.Proofs13PartitionSelection

/-!
# The small-target case of Lemma 13.7

If the requested real-power length is at most two, partition the ambient
progression into cells of length two or three (or keep it whole when already
short). Freiman relations make every such cell affine on the base-row domain.
This gives Stage 13.7 without the large-scale Corollary 7.11 threshold.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.GowersSzemeredi

/-- A short-target affine partition of the base row needs no density or
large-scale hypothesis. -/
theorem stage137_affine_base_partition_small {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (F : Stage136Data N)
    (hproper : F.R.IsProper) (hstep : F.R.step != 0) (hlen : 0 < F.R.length)
    (hsmall : (F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) ≤ 2) (y : ZMod N) :
    Stage137AffineBasePartition S F y := by
  classical
  let A := F.R.carrier.filter fun x ↦ (x, y) ∈ S.A
  have hα := S.alpha_pos
  have hexp : (2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448 ≤ 1 := by
    calc
      _ ≤ (2 : Real) ^ (-(100 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ hα.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  have hlength : (F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) ≤ F.R.length :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hlen) hexp
  obtain ⟨M, P, hP, hcell⟩ := short_modular_affine_partition F.R A
    (fun x ↦ S.phi (x, y)) hproper hstep
    (section13_base_row_freiman S F.R.carrier y) hsmall hlength
  refine ⟨M, P, hP, ?_⟩
  intro j
  obtain ⟨hs, hp, hl, a, b, hlin⟩ := hcell j
  refine ⟨hs, hp, hl, a, b, ?_⟩
  intro x hx
  obtain ⟨hxP, hxA⟩ := Finset.mem_filter.mp hx
  exact hlin x (Finset.mem_filter.mpr
    ⟨hxP, Finset.mem_filter.mpr ⟨hP.cell_subset j hxP, hxA⟩⟩)

/-- Lemma 13.7 when the requested real-power lower length is at most two. -/
theorem lemma_13_7_small_scale {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (hF : IsStage136Data S D E F)
    (hsmall : (F.R.length : Real) ^
      ((2 : Real) ^ (-(100 : Int)) * S.alpha ^ 448) ≤ 2) :
    ∃ G : Stage137Data N, IsStage137Data S D E F G := by
  apply lemma_13_7_of_affine_base_partitions S D E F hF
  have hR := stage136_progression_nonempty S D E F hF
  have hcard : F.R.carrier.card = F.R.length := hF.2.2.1
  have hlen : 0 < F.R.length := by simpa only [hcard] using hR.card_pos
  exact fun y _ ↦ stage137_affine_base_partition_small S F hF.2.2.1 hF.2.1 hlen hsmall y

end LeanProofs.GowersSzemeredi
