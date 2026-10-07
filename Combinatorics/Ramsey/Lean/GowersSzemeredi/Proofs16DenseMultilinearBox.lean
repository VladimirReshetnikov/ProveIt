import GowersSzemeredi.Proofs16AffineClasses
import GowersSzemeredi.Proofs13CoefficientPartition

/-! The finite averaging step in Corollary 16.11: a multiply-linear graph
on a dense domain yields one dense multilinear piece in one proper box. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Select one graph from a finite cover, charging its actual real upper
count. Overlapping graphs are first made into disjoint classes. -/
theorem finite_graph_cover_dense_piece {X Y : Type*} [DecidableEq X]
    {q : Nat} (hq : 0 < q) (B : Finset X) (f : X → Y) (mu : Fin q → X → Y)
    (hcover : ∀ x ∈ B, ∃ i, f x = mu i x)
    {Q d mass : Real} (hQ : (q : Real) ≤ Q) (hd : 0 ≤ d) (hmass : 0 ≤ mass)
    (hB : d * mass ≤ B.card) :
    ∃ i : Fin q, ∃ C : Finset X,
      C ⊆ B ∧ d / Q * mass ≤ C.card ∧ ∀ x ∈ C, f x = mu i x := by
  classical
  obtain ⟨C, hpart, hC⟩ := finite_graph_cover_partition hq B f mu hcover
  have hqpos : (0 : Real) < q := by exact_mod_cast hq
  have hQpos : 0 < Q := hqpos.trans_le hQ
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hs : (∑ _i : Fin q, d / Q * mass) ≤ ∑ i : Fin q, ((C i).card : Real) := by
    calc
      _ = (q : Real) * (d / Q * mass) := by simp
      _ ≤ Q * (d / Q * mass) := mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = d * mass := by field_simp
      _ ≤ B.card := hB
      _ = _ := by rw [← Nat.cast_sum, hpart.sum_card]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hs
  exact ⟨i, C i, hpart.cell_subset i, hi, hC i⟩

/-- Applying multiple multilinearity at half the original density produces
one proper box and one multilinear graph of the expected relative mass.
This retains the exact width exponent and reciprocal graph-count factor. -/
theorem MultiplyLinearFunction.dense_multilinear_box {N k : Nat} [NeZero N]
    {gamma r delta : Real} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (B : Finset (Point N k)) (phi : Point N k → ZMod N)
    (hML : MultiplyLinearFunction gamma r B phi)
    (P : Box N k) (hP : P.IsProper) (hPne : P.carrier.Nonempty)
    (hBsub : B ⊆ P.carrier) (hBmass : delta * P.carrier.card ≤ B.card) :
    ∃ Q : Box N k, ∃ C : Finset (Point N k), ∃ mu : Point N k → ZMod N,
      Q.IsProper ∧ Q.carrier ⊆ P.carrier ∧
      (P.width : Real) ^ ((multipleC (r⁻¹ * (delta / 2)) gamma k) ^ r) ≤ Q.width ∧
      C ⊆ B ∧ C ⊆ Q.carrier ∧
      (delta / 2) / ((multipleQ (r⁻¹ * (delta / 2)) gamma k) ^ r) * Q.carrier.card ≤ C.card ∧
      IsMultilinear mu ∧ ∀ x ∈ C, phi x = mu x := by
  classical
  obtain ⟨M, q, H, Q, mu, hHsub, hHmass, hpart, hproper, hqbound, hwidth, hmu, hcover⟩ :=
    hML (delta / 2) (by positivity) (by linarith) P hP
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
