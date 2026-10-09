import GowersSzemeredi.Proofs16HigherColumnTupleProjection

/-! Sparse bad anchor quadruples and bad eight-column relations remove
only a controlled mass of higher arrangements. This uses their actual
projection fibres, rather than assuming uniformity of the given family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementBadData {N : Nat} (H B : Finset (HigherArrangementParameter N))
    (E : Finset (Fin 4 → ZMod N)) (VL VR : Finset (Fin 8 → ZMod N)) :
    Finset (HigherArrangementParameter N) :=
  ((Finset.univ.biUnion fun j : Fin 4 => H.filter fun p => higherArrangementAnchorQuadruple p j ∈ E) ∪
    (H.filter fun p => higherArrangementLeftColumns p ∈ VL)) ∪
    (H.filter fun p => higherArrangementRightColumns p ∈ VR) ∪ (H ∩ B)

def higherArrangementAvoidingBadData {N : Nat} (H B : Finset (HigherArrangementParameter N))
    (E : Finset (Fin 4 → ZMod N)) (VL VR : Finset (Fin 8 → ZMod N)) :
    Finset (HigherArrangementParameter N) := H \ higherArrangementBadData H B E VL VR

theorem mem_higherArrangementAvoidingBadData {N : Nat}
    (H B : Finset (HigherArrangementParameter N)) (E : Finset (Fin 4 → ZMod N))
    (VL VR : Finset (Fin 8 → ZMod N)) (p : HigherArrangementParameter N) :
    p ∈ higherArrangementAvoidingBadData H B E VL VR ↔
      p ∈ H ∧ (∀ j, higherArrangementAnchorQuadruple p j ∉ E) ∧
        higherArrangementLeftColumns p ∉ VL ∧ higherArrangementRightColumns p ∉ VR ∧ p ∉ B := by
  by_cases hp : p ∈ H
  · simp [higherArrangementAvoidingBadData,higherArrangementBadData,hp,not_or]
  · simp [higherArrangementAvoidingBadData,higherArrangementBadData,hp]

theorem higher_arrangement_bad_data_card_le {N : Nat} [NeZero N]
    (H B : Finset (HigherArrangementParameter N)) (E : Finset (Fin 4 → ZMod N))
    (VL VR : Finset (Fin 8 → ZMod N)) :
    (higherArrangementBadData H B E VL VR).card ≤
      4*E.card*N^8+(VL.card+VR.card)*N^4+B.card := by
  let A := Finset.univ.biUnion fun j : Fin 4 => H.filter fun p => higherArrangementAnchorQuadruple p j ∈ E
  let L := H.filter fun p => higherArrangementLeftColumns p ∈ VL
  let R := H.filter fun p => higherArrangementRightColumns p ∈ VR
  have hA : A.card ≤ 4*E.card*N^8 := by
    calc A.card ≤ ∑ j : Fin 4, (H.filter fun p => higherArrangementAnchorQuadruple p j ∈ E).card :=
           Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin 4, E.card*N^8 := Finset.sum_le_sum fun j _ =>
           higher_arrangements_anchor_quadruple_card_le _ E j (fun p hp => (Finset.mem_filter.mp hp).2)
      _ = _ := by simp [Nat.mul_assoc]
  have hL := higher_arrangements_left_columns_card_le L VL (fun p hp => (Finset.mem_filter.mp hp).2)
  have hR := higher_arrangements_right_columns_card_le R VR (fun p hp => (Finset.mem_filter.mp hp).2)
  have hB : (H ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have h1 := Finset.card_union_le A L
  have h2 := Finset.card_union_le (A ∪ L) R
  have h3 := Finset.card_union_le (A ∪ L ∪ R) (H ∩ B)
  change (A ∪ L ∪ R ∪ (H ∩ B)).card ≤ _
  rw [Nat.add_mul]
  omega

theorem higher_arrangements_avoiding_bad_data_mass {N : Nat} [NeZero N]
    (H B : Finset (HigherArrangementParameter N)) (E : Finset (Fin 4 → ZMod N))
    (VL VR : Finset (Fin 8 → ZMod N)) {kappa eps etaL etaR delta : Real}
    (hH : kappa*(N : Real)^11 ≤ H.card) (hE : (E.card : Real) ≤ eps*(N : Real)^3)
    (hL : (VL.card : Real) ≤ etaL*(N : Real)^7)
    (hR : (VR.card : Real) ≤ etaR*(N : Real)^7)
    (hB : (B.card : Real) ≤ delta*(N : Real)^11) :
    (kappa-4*eps-etaL-etaR-delta)*(N : Real)^11 ≤
      (higherArrangementAvoidingBadData H B E VL VR).card := by
  have hbad : ((higherArrangementBadData H B E VL VR).card : Real) ≤
      4*(E.card : Real)*(N : Real)^8+((VL.card : Real)+(VR.card : Real))*(N : Real)^4+(B.card : Real) := by
    exact_mod_cast higher_arrangement_bad_data_card_le H B E VL VR
  have hquad := mul_le_mul_of_nonneg_right hE (show 0 ≤ (N : Real)^8 by positivity)
  have hleft := mul_le_mul_of_nonneg_right hL (show 0 ≤ (N : Real)^4 by positivity)
  have hright := mul_le_mul_of_nonneg_right hR (show 0 ≤ (N : Real)^4 by positivity)
  have hbad' : ((higherArrangementBadData H B E VL VR).card : Real) ≤
      (4*eps+etaL+etaR+delta)*(N : Real)^11 := by
    nlinarith only [hbad,hquad,hleft,hright,hB]
  have hpartition := Finset.card_sdiff_add_card_inter H (higherArrangementBadData H B E VL VR)
  have hinter : (H ∩ higherArrangementBadData H B E VL VR).card ≤
      (higherArrangementBadData H B E VL VR).card := Finset.card_le_card Finset.inter_subset_right
  have htotal : (H.card : Real) ≤ (higherArrangementAvoidingBadData H B E VL VR).card+
      ((higherArrangementBadData H B E VL VR).card : Real) := by
    exact_mod_cast (show H.card ≤ (H \ higherArrangementBadData H B E VL VR).card+
      (higherArrangementBadData H B E VL VR).card by omega)
  nlinarith only [hH,hbad',htotal]

end LeanProofs.GowersSzemeredi
