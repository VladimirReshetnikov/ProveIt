import GowersSzemeredi.Proofs13CommonStepCover
import GowersSzemeredi.Proofs16BoxGeometry

/-! Equal-side covers of proper boxes in arbitrary dimension. Padded cells
may extend beyond the original box, but the selected dense set remains a
subset of the original set. The capacity loss is at most 2^k. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

theorem Box.card_eq_prod_axis_card {N k : Nat} [NeZero N] (P : Box N k) :
    P.carrier.card = ∏ i, (P.axis i).carrier.card := by
  classical
  have heq : P.carrier = Fintype.piFinset (fun i => (P.axis i).carrier) := by
    ext x
    simp [Box.carrier]
  rw [heq, Fintype.card_piFinset]

/-- Index one padded common-step interval independently on every axis. -/
def Box.equalSideCoverIndex {N k : Nat} (P : Box N k) (m : Nat) :=
  (i : Fin k) → Fin 1 × Fin ((P.axis i).length / (1 * m) + 1)

instance {N k : Nat} (P : Box N k) (m : Nat) : Fintype (P.equalSideCoverIndex m) :=
  Pi.instFintype

instance {N k : Nat} (P : Box N k) (m : Nat) : Nonempty (P.equalSideCoverIndex m) :=
  ⟨fun _ => (0, ⟨0, Nat.zero_lt_succ _⟩)⟩

/-- Every output axis has length exactly m and the original common step. -/
def Box.equalSideCoverCell {N k : Nat} (P : Box N k) (m : Nat)
    (j : P.equalSideCoverIndex m) : Box N k where
  axis i := commonStepCoverCell (P.axis i) 1 m (j i)
  commonDiff := P.commonDiff
  axis_step i := by simp only [commonStepCoverCell, Nat.cast_one, one_mul]; exact P.axis_step i

theorem Box.equalSideCover_covers {N k m : Nat} [NeZero N]
    (P : Box N k) (hm : 0 < m) {x : Point N k} (hx : x ∈ P.carrier) :
    ∃ j : P.equalSideCoverIndex m, x ∈ (P.equalSideCoverCell m j).carrier := by
  classical
  have hxi : ∀ i, x i ∈ (P.axis i).carrier := by simpa [Box.carrier] using hx
  choose j hj using fun i => commonStepCoverCell_covers (P.axis i) (by omega : 0 < 1) hm (hxi i)
  exact ⟨j, by simpa [Box.carrier, Box.equalSideCoverCell] using hj⟩

theorem Box.equalSideCover_capacity {N k m : Nat} [NeZero N]
    (P : Box N k) (hP : P.IsProper) (hm : m ≤ P.width) :
    Fintype.card (P.equalSideCoverIndex m) * m ^ k ≤ 2 ^ k * P.carrier.card := by
  classical
  have hcap (i : Fin k) : (1 * ((P.axis i).length / (1 * m) + 1)) * m ≤
      2 * (P.axis i).carrier.card := by
    rw [hP i]
    exact commonStepCoverCell_capacity _ 1 m (by simpa only [one_mul] using hm.trans (P.width_le_axis_length i))
  have h := Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hcap i)
  simpa only [Box.equalSideCoverIndex, Fintype.card_pi, Fintype.card_prod, Fintype.card_fin,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← P.card_eq_prod_axis_card] using h

/-- A dense subset of a proper box has a dense piece in a box of any
prescribed positive side length up to the original width. -/
theorem Box.dense_equal_side_box {N k m : Nat} [Fact N.Prime]
    (P : Box N k) (hP : P.IsProper) (hstep : P.commonDiff != 0)
    (hm : 0 < m) (hmP : m ≤ P.width) (B : Finset (Point N k))
    {delta : Real} (hδ : 0 ≤ delta) (hB : B ⊆ P.carrier)
    (hmass : delta * P.carrier.card ≤ B.card) :
    ∃ Q : Box N k, ∃ C : Finset (Point N k),
      Q.commonDiff = P.commonDiff ∧ Q.IsProper ∧ (∀ i, (Q.axis i).length = m) ∧
      C ⊆ B ∧ C ⊆ Q.carrier ∧ delta / (2 : Real) ^ k * (m : Real) ^ k ≤ C.card := by
  classical
  let I := P.equalSideCoverIndex m
  let Q : I → Box N k := P.equalSideCoverCell m
  let C : I → Finset (Point N k) := fun j => B ∩ (Q j).carrier
  have hcover : B ⊆ Finset.univ.biUnion C := by
    intro x hx
    obtain ⟨j, hj⟩ := P.equalSideCover_covers hm (hB hx)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hj⟩⟩
  have hcount : (B.card : Real) ≤ ∑ j : I, ((C j).card : Real) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcap : (Fintype.card I : Real) * (m : Real) ^ k ≤ (2 : Real) ^ k * P.carrier.card := by
    exact_mod_cast P.equalSideCover_capacity hP hmP
  have hsum : ∑ _j : I, delta / (2 : Real) ^ k * (m : Real) ^ k ≤
      ∑ j : I, ((C j).card : Real) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h := mul_le_mul_of_nonneg_left hcap (div_nonneg hδ (by positivity : (0 : Real) ≤ 2 ^ k))
    have h2 : (2 : Real) ^ k ≠ 0 := by positivity
    calc
      _ = (delta / (2 : Real) ^ k) * ((Fintype.card I : Real) * (m : Real) ^ k) := by ring
      _ ≤ (delta / (2 : Real) ^ k) * ((2 : Real) ^ k * P.carrier.card) := h
      _ = delta * P.carrier.card := by field_simp
      _ ≤ B.card := hmass
      _ ≤ _ := hcount
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  have hmN : m ≤ N := hmP.trans (P.width_le_modulus hP)
  refine ⟨Q j, C j, rfl, ?_, fun _ => rfl, Finset.inter_subset_left, Finset.inter_subset_right, hj⟩
  intro i
  apply ModAP.isProper_of_prime_step _ ?_ hmN
  simpa only [Q, Box.equalSideCoverCell, commonStepCoverCell, Nat.cast_one, one_mul, P.axis_step] using hstep

end LeanProofs.GowersSzemeredi
