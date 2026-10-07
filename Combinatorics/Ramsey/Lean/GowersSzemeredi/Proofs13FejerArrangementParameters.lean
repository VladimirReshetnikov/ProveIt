import GowersSzemeredi.Proofs13FejerFeatureLine
import GowersSzemeredi.Sections12_13

/-! An exact 32-parameter encoding of catalogue order-eight arrangements
whose horizontal coordinates satisfy the additive relation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private theorem fejer_last_index : finSuccEquivLast (15 : Fin 16) = none := finSuccEquivLast_last

def fejerArrangementSign {N : Nat} (i : Fin 16) : ZMod N := if i.val < 8 then 1 else -1

def fejerArrangementFreeSign {N : Nat} (i : Fin 15) : ZMod N := fejerArrangementSign i.castSucc

theorem fejerArrangementFreeSign_ne_zero {N : Nat} [NeZero N] [Fact N.Prime]
    (i : Fin 15) : fejerArrangementFreeSign (N := N) i ≠ 0 := by
  unfold fejerArrangementFreeSign fejerArrangementSign
  split_ifs <;> simp

theorem fejerArrangement_additive_iff {N : Nat} (x : Fin 16 → ZMod N) :
    IsAdditiveTuple (k := 8) x ↔ ∑ i, fejerArrangementSign i * x i = 0 := by
  classical
  have hs : (∑ i, fejerArrangementSign i * x i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin 16 => i.val < 8), x i) -
      ∑ i ∈ Finset.univ.filter (fun i : Fin 16 => 8 ≤ i.val), x i := by
    simp only [fejerArrangementSign, ite_mul, one_mul, neg_one_mul]
    rw [Finset.sum_ite]
    simp only [not_lt, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hs, sub_eq_zero]
  rfl

theorem fejerArrangement_additive_last {N : Nat} (x : Fin 16 → ZMod N) :
    IsAdditiveTuple (k := 8) x ↔
      x (Fin.last 15) = ∑ i : Fin 15, fejerArrangementFreeSign i * x i.castSucc := by
  rw [fejerArrangement_additive_iff, Fin.sum_univ_castSucc]
  change ((∑ i : Fin 15, fejerArrangementFreeSign i * x i.castSucc) + (-1) * x (Fin.last 15) = 0) ↔ _
  rw [neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]
  exact eq_comm

abbrev FejerArrangementParameters (N : Nat) := BalancedFeatureVariable (Fin 15) → ZMod N

def fejerArrangementDecode {N : Nat} (z : FejerArrangementParameters N) : DArrangement N 8 :=
  ((fun i => balancedHorizontal fejerArrangementFreeSign (fun j => z (some (Sum.inl j))) (finSuccEquivLast i)),
    (fun i => z (some (Sum.inr (finSuccEquivLast i)))), z none)

def fejerArrangementEncode {N : Nat} (R : DArrangement N 8) : FejerArrangementParameters N :=
  balancedFeatureAssignment (fun i => R.x i.castSucc)
    (fun j => R.y (finSuccEquivLast.symm j)) R.height

theorem fejerArrangementDecode_additive {N : Nat} (z : FejerArrangementParameters N) :
    IsAdditiveTuple (fejerArrangementDecode z).x := by
  rw [fejerArrangement_additive_last]
  simp [fejerArrangementDecode, DArrangement.x, balancedHorizontal, fejer_last_index]

theorem fejerArrangementEncode_decode {N : Nat} (z : FejerArrangementParameters N) :
    fejerArrangementEncode (fejerArrangementDecode z) = z := by
  funext i
  rcases i with _ | (j | j) <;>
    simp [fejerArrangementEncode, fejerArrangementDecode, balancedFeatureAssignment,
      DArrangement.x, DArrangement.y, DArrangement.height, balancedHorizontal]

theorem fejerArrangementDecode_encode {N : Nat} (R : DArrangement N 8)
    (hR : IsAdditiveTuple R.x) : fejerArrangementDecode (fejerArrangementEncode R) = R := by
  have hx : (fejerArrangementDecode (fejerArrangementEncode R)).x = R.x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [fejerArrangementDecode, fejerArrangementEncode, DArrangement.x,
        balancedFeatureAssignment, balancedHorizontal, fejer_last_index] using
        ((fejerArrangement_additive_last R.x).mp hR).symm
    · simp [fejerArrangementDecode, fejerArrangementEncode, DArrangement.x,
        balancedFeatureAssignment, balancedHorizontal]
  have hy : (fejerArrangementDecode (fejerArrangementEncode R)).y = R.y := by
    funext i
    simp [fejerArrangementDecode, fejerArrangementEncode, DArrangement.y, balancedFeatureAssignment]
  have hh : (fejerArrangementDecode (fejerArrangementEncode R)).height = R.height := rfl
  exact Prod.ext hx (Prod.ext hy hh)

abbrev FejerBalancedArrangement (N : Nat) := {R : DArrangement N 8 // IsAdditiveTuple R.x}

noncomputable instance fejerBalancedArrangementFintype (N : Nat) [NeZero N] :
    Fintype (FejerBalancedArrangement N) := by
  classical
  infer_instance

def fejerArrangementParametersEquiv {N : Nat} :
    FejerArrangementParameters N ≃ FejerBalancedArrangement N where
  toFun z := ⟨fejerArrangementDecode z, fejerArrangementDecode_additive z⟩
  invFun R := fejerArrangementEncode R.1
  left_inv := fejerArrangementEncode_decode
  right_inv R := Subtype.ext (fejerArrangementDecode_encode R.1 R.2)

theorem fejerBalancedArrangement_card {N : Nat} [NeZero N] :
    Fintype.card (FejerBalancedArrangement N) = N ^ 32 := by
  rw [← Fintype.card_congr (fejerArrangementParametersEquiv (N := N))]
  simp only [FejerArrangementParameters, Fintype.card_fun, ZMod.card, balancedFeatureVariable_card,
    Fintype.card_fin]

end LeanProofs.GowersSzemeredi
