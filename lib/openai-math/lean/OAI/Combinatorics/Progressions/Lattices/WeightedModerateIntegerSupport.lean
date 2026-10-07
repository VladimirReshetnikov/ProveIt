import OAI.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def weightedModerateJetBound {B : Type*} [Fintype B] {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (offset : B → ℤ) (S : Finset I) : ℤ :=
  ∑ b, (|offset b| + (c b).length) *
    ((2 : ℤ) ^ S.card * ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) * (s b j).length)

theorem weightedModerateIntegerBlock_bound {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) (offset : ℤ)
    (x : IntegerScalarCubeBox Empty c.length × (∀ j, IntegerScalarCubeBox I (s j).length)) (S : J) :
    |weightedModerateIntegerBlock c s J offset x S| ≤ (|offset| + c.length) *
      ((2 : ℤ) ^ S.val.card * ∏ j, ((Fintype.card I + 1 : ℕ) : ℤ) * (s j).length) := by
  have hc : |offset + (x.1 none : ℤ)| ≤ |offset| + c.length :=
    (abs_add_le _ _).trans (add_le_add le_rfl (integerScalarCubeBox_coordinate_abs x.1 none))
  have hj := integerBooleanBlockJet_bound (fun j r => (x.2 j r : ℤ)) (fun j => (s j).length)
    (fun j r => integerScalarCubeBox_coordinate_abs (x.2 j) r) S.val
  unfold weightedModerateIntegerBlock
  rw [abs_mul]
  exact mul_le_mul hc hj (abs_nonneg _) (by positivity)

theorem weightedModerateIntegerJetSum_bound {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift : J → ℤ)
    (x : ∀ b, IntegerScalarCubeBox Empty (c b).length × (∀ j, IntegerScalarCubeBox I (s b j).length))
    (S : J) : |weightedModerateIntegerJetSum c s J offset shift x S - shift S| ≤
      weightedModerateJetBound c s offset S := by
  classical
  simp only [weightedModerateIntegerJetSum, Pi.add_apply, Finset.sum_apply, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun b _ => weightedModerateIntegerBlock_bound (c b) (s b) J (offset b) (x b) S)

theorem weightedModerateIntegerGridMass_eq {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
    (J : Finset (Finset I)) (offset : B → ℤ) (shift z : J → ℤ) (M : ℕ)
    (hM : ∀ S : J, 2 * weightedModerateJetBound c s offset S < (M : ℤ))
    (hz : ∀ S : J, |z S - shift S| ≤ weightedModerateJetBound c s offset S) :
    integerGridMass (weightedModerateIntegerProductSource c s)
      (weightedModerateIntegerJetSum c s J offset shift) M z =
        finiteImageMass (weightedModerateIntegerProductSource c s)
          (weightedModerateIntegerJetSum c s J offset shift) z := by
  apply integerGridMass_eq_imageMass
  intro x _ S
  have hy := abs_le.mp (weightedModerateIntegerJetSum_bound c s J offset shift x S)
  have hz' := abs_le.mp (hz S)
  have hM' := hM S
  rw [abs_lt]
  constructor <;> omega

end Erdos3

end

end OAI
