import PA194PAeqTermSubstGrowth

/-! Numeric growth of substituted arithmetic term vectors and relation codes,
valid in every IΣ₁ model, including malformed inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqTermSubstVecGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessRepeatVec PRAWitnessTermFunctions PA194PAeqTermSubstGrowth

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termSubstVec_le (k w v : V) :
    termSubstVec PA194PAeq.language k w v ≤ repeatVec (tau (w + v + 8) (20 * v + 20)) k := by
  by_cases hv : IsUTermVec PA194PAeq.language k v
  · have h := len_repeatVec_of_nth_le (v := termSubstVec PA194PAeq.language k w v)
      (m := tau (w + v + 8) (20 * v + 20)) (fun i hi => by
        have hi' : i < k := by simpa [len_termSubstVec hv] using hi
        rw [nth_termSubstVec hv hi']
        exact le_trans (termSubst_le w v.[i])
          (tau_mono (add_le_add (add_le_add le_rfl (nth_le v i)) le_rfl)
            (add_le_add (mul_le_mul' le_rfl (nth_le v i)) le_rfl)))
    simpa [len_termSubstVec hv] using h
  · simp [termSubstVec, hv]

theorem relation_le (tag k r w v : V) (htag : tag ≤ 1) :
    ⟪tag, k, r, termSubstVec PA194PAeq.language k w v⟫ + 1 ≤
      tau (w + v + k + r + 8) (20 * v + 2 * k + 26) := by
  let X : V := w + v + k + r + 8
  let D : V := 20 * v + 20 + 2 * k
  have hX : w + v + 8 ≤ X := by
    dsimp [X]
    calc w + v + 8 ≤ w + v + 8 + (k + r) := le_self_add
      _ = w + v + k + r + 8 := by ring
  have hv : termSubstVec PA194PAeq.language k w v ≤ tau X D := by
    apply le_trans (termSubstVec_le k w v)
    apply le_trans (repeatVec_mono_left (tau_mono hX le_rfl) k)
    simpa [D] using (repeatVec_le_tau (le_refl (tau X (20 * v + 20))) k)
  have hk : k ≤ tau X D := le_trans (by
    dsimp [X]
    calc k ≤ (w + v) + k := le_add_self
      _ ≤ w + v + k + r + 8 := le_trans le_self_add le_self_add) (le_tau _ _)
  have hr : r ≤ tau X D := le_trans (by
    dsimp [X]
    exact le_trans le_add_self le_self_add) (le_tau _ _)
  have ht : tag ≤ tau X D := le_trans htag (le_trans (by norm_num) (four_le_tau _ _))
  have hc := code4_le_tau ht hk hr hv
  apply le_trans hc
  apply tau_mono le_rfl
  dsimp [D]
  exact le_of_eq (by ring)

#print axioms termSubstVec_le
#print axioms relation_le
end PA194PAeqTermSubstVecGrowth
