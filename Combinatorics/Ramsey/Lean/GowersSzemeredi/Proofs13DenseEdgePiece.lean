import GowersSzemeredi.Proofs13DenseBilinearExtension

/-! Large-density bilinear pieces give the original printed vertical-edge
mass and a global short-difference rule, independent of the height. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_shift_overlap_card {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] (A : Finset G) (d : G) :
    2 * A.card ≤ (A.filter fun x ↦ x + d ∈ A).card + Fintype.card G := by
  classical
  let R := A.image (fun x ↦ x - d)
  have hR : R.card = A.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    simpa using congrArg (fun z ↦ z + d) hxy
  have hmem (x : G) : x + d ∈ A ↔ x ∈ R := by
    constructor
    · intro hx
      exact Finset.mem_image.mpr ⟨x + d, hx, by simp⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
      rw [← hxy]
      simpa using hy
  have heq : A.filter (fun x ↦ x + d ∈ A) = A ∩ R := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, hmem]
  have h := Finset.card_inter_add_card_union A R
  have hu := Finset.card_le_univ (A ∪ R)
  rw [hR] at h
  rw [heq]
  omega

theorem section13_dense_row_edges_mass {N : Nat} [NeZero N]
    (S : Section13Context N) (h : ZMod N) :
    (12 * S.alpha - 11) * (N : Real) ^ 2 ≤
      (verticalEdgeDomain (section13DenseRowPiece S.A) h).card := by
  classical
  let B := section13DenseRowPiece S.A
  have heq : verticalEdgeDomain B h = B.filter (fun z ↦ z + (0, h) ∈ B) := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [verticalEdgeDomain, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk_add_mk, add_zero]
  have hNat : 2 * B.card ≤ (verticalEdgeDomain B h).card + N ^ 2 := by
    have h := finite_shift_overlap_card B (0, h)
    simpa only [← heq, Fintype.card_prod, ZMod.card, pow_two] using h
  have hR : 2 * (B.card : Real) ≤ (verticalEdgeDomain B h).card + (N : Real) ^ 2 := by
    exact_mod_cast hNat
  have hB := section13_dense_row_piece_mass S
  change (6 * S.alpha - 5) * (N : Real) ^ 2 ≤ (B.card : Real) at hB
  change (12 * S.alpha - 11) * (N : Real) ^ 2 ≤ (verticalEdgeDomain B h).card
  nlinarith only [hR, hB]

/-- A bilinear agreement gives the same linear vertical-difference rule
on every height-edge domain, without a Bohr restriction. -/
theorem bilinear_vertical_difference_rule {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) (hB : BilinearOn B phi) :
    ∃ c : ZMod N, ∀ h v, v ∈ verticalEdgeDomain B h →
      ∀ w, w ∈ verticalEdgeDomain B h →
      verticalPhiDifference phi h v - verticalPhiDifference phi h w =
        (c * h) * (v.1 - w.1) := by
  obtain ⟨mu, ⟨c00, c10, c01, c11, hmu⟩, hphi⟩ := hB
  refine ⟨c11, fun h v hv w hw ↦ ?_⟩
  obtain ⟨hv0, hv1⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨hw0, hw1⟩ := (Finset.mem_filter.mp hw).2
  unfold verticalPhiDifference
  rw [hphi _ hv1, hphi _ hv0, hphi _ hw1, hphi _ hw0,
    hmu, hmu, hmu, hmu]
  ring

/-- All heights have the original printed mass in the remaining density
range, and one global bilinear coefficient supplies every difference rule. -/
theorem section13_printed_high_density_edge_rules {N : Nat} [Fact N.Prime]
    (hN : 5 ≤ N) (S : Section13Context N) (hα : 14 / 15 < S.alpha) :
    ∃ Y : ZMod N → Finset (Pair N), ∃ c : ZMod N,
      ∀ h, Y h ⊆ verticalEdgeDomain S.A h ∧
        (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 * (N : Real) ^ 2 ≤ (Y h).card ∧
        ∀ v ∈ Y h, ∀ w ∈ Y h,
          verticalPhiDifference S.phi h v - verticalPhiDifference S.phi h w =
            (c * h) * (v.1 - w.1) := by
  classical
  let B := section13DenseRowPiece S.A
  have hBsub : B ⊆ S.A := Finset.filter_subset _ _
  have hB : BilinearOn B S.phi := section13_dense_row_piece_bilinear hN S hα
  obtain ⟨c, hrule⟩ := bilinear_vertical_difference_rule B S.phi hB
  refine ⟨fun h ↦ verticalEdgeDomain B h, c, fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · intro v hv
    obtain ⟨hv0, hv1⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBsub hv0, hBsub hv1⟩
  · have hcoef : (2 : Real) ^ (-(26 : Int)) * S.alpha ^ 128 ≤ 1 / 5 := by
      calc
        _ ≤ (2 : Real) ^ (-(26 : Int)) * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one) (by positivity)
        _ ≤ 1 / 5 := by norm_num
    have hlarge : (1 / 5 : Real) ≤ 12 * S.alpha - 11 := by linarith
    exact ((mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hlarge (sq_nonneg _))).trans
      (section13_dense_row_edges_mass S h)
  · exact hrule h

end LeanProofs.GowersSzemeredi
