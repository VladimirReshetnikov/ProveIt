import GowersSzemeredi.Proofs16DenseMultilinearBox
import GowersSzemeredi.Proofs16PowerCoverTransport

/-! Dense graph selection from a cover with arbitrary explicit controls.
The exact reciprocal graph-count loss is independent of the width exponent. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem LargeBoxMultilinearCover.dense_multilinear_box {N k : Nat} [NeZero N]
    {delta C e T : Real} (hdelta : 0 < delta)
    (B : Finset (Point N k)) (phi : Point N k → ZMod N)
    (hML : LargeBoxMultilinearCover (partialGraph B phi) (delta / 2) C e T)
    (P : Box N k) (hP : P.IsProper) (hPne : P.carrier.Nonempty)
    (hT : T ≤ (P.width : Real))
    (hBsub : B ⊆ P.carrier) (hBmass : delta * P.carrier.card ≤ B.card) :
    ∃ Q : Box N k, ∃ A : Finset (Point N k), ∃ mu : Point N k → ZMod N,
      Q.IsProper ∧ Q.carrier ⊆ P.carrier ∧
      (P.width : Real) ^ e ≤ Q.width ∧ A ⊆ B ∧ A ⊆ Q.carrier ∧
      (delta / 2) / C * Q.carrier.card ≤ A.card ∧
      IsMultilinear mu ∧ ∀ x ∈ A, phi x = mu x := by
  classical
  obtain ⟨M, q, H, Q, mu, hHsub, hHmass, hpart, hproper, hqbound, hwidth, hmu, hcover⟩ :=
    hML P hP hT
  have hBHmass : delta / 2 * P.carrier.card ≤ (B ∩ H).card := by
    have hu : (B ∪ H).card ≤ P.carrier.card :=
      Finset.card_le_card (Finset.union_subset hBsub hHsub)
    have hi := Finset.card_union_add_card_inter B H
    have hiR : ((B ∪ H).card : Real) + (B ∩ H).card = B.card + H.card := by exact_mod_cast hi
    have huR : ((B ∪ H).card : Real) ≤ P.carrier.card := by exact_mod_cast hu
    nlinarith only [hBmass, hHmass, hiR, huR]
  have hBHne : (B ∩ H).Nonempty := by
    apply Finset.card_pos.mp
    have hPc : (0 : Real) < P.carrier.card := by exact_mod_cast hPne.card_pos
    have hpos := (mul_pos (div_pos hdelta (by norm_num)) hPc).trans_le hBHmass
    exact_mod_cast hpos
  obtain ⟨x, hx⟩ := hBHne
  obtain ⟨j, hj⟩ := (hpart.1 x).mp (hBsub (Finset.mem_inter.mp hx).1)
  have hpoint : (x, phi x) ∈ partialGraph B phi :=
    Finset.mem_image.mpr ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩
  obtain ⟨i, _⟩ := hcover j x hj (Finset.mem_inter.mp hx).2 (phi x) hpoint
  have hq : 0 < q := Nat.zero_lt_of_lt i.isLt
  obtain ⟨j, hjmass⟩ := exists_coordinate_filter_cell (B ∩ H) P.carrier id
    (fun j ↦ (Q j).carrier) hPne hpart
    (fun x hx ↦ hBsub (Finset.mem_inter.mp hx).1) hBHmass
  let A := (B ∩ H).filter fun x ↦ x ∈ (Q j).carrier
  have hAcover : ∀ x ∈ A, ∃ i, phi x = mu j i x := by
    intro x hx
    obtain ⟨hxBH, hxQ⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxB, hxH⟩ := Finset.mem_inter.mp hxBH
    exact hcover j x hxQ hxH (phi x) (Finset.mem_image.mpr ⟨x, hxB, rfl⟩)
  obtain ⟨i, C, hCA, hmassC, hagree⟩ := finite_graph_cover_dense_piece hq A phi (mu j)
    hAcover hqbound (by positivity : 0 ≤ delta / 2) (Nat.cast_nonneg (Q j).carrier.card) hjmass
  refine ⟨Q j, C, mu j i, hproper j, hpart.cell_subset j, hwidth j, ?_, ?_, hmassC, hmu j i, hagree⟩
  · exact fun x hx ↦ (Finset.mem_inter.mp (Finset.mem_filter.mp (hCA hx)).1).1
  · exact fun x hx ↦ (Finset.mem_filter.mp (hCA hx)).2


end LeanProofs.GowersSzemeredi
