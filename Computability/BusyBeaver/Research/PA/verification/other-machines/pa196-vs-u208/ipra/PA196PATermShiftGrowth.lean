import PA196PATermBShiftGrowth

/-! Arithmetic free-variable shifting has an explicit double-exponential
all-model growth bound. Arithmetic function symbols have arity at most two. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PATermShiftGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessRepeatVec PRAWitnessTermFunctions

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termShift_le (t : V) : termShift ℒₒᵣ t ≤ tau (t + 8) (20 * t + 20) := by
  by_cases ht : IsUTerm ℒₒᵣ t
  · apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
    · definability
    · intro z
      rw [termShift_bvar]
      exact le_trans (le_trans le_self_add (le_tau _ _))
        (tau_mono le_rfl (le_refl _))
    · intro x
      rw [termShift_fvar]
      have hx : x + 1 ≤ ^&x := lt_iff_succ_le.mp (var_lt_qqFvar x)
      have hc := code2_le_tau (le_tau_of (^&x) 1 0 (le_trans (by norm_num : (1 : V) ≤ 8) le_add_self))
        (le_tau_of (^&x) (x+1) 0 (le_trans hx le_self_add))
      apply le_trans (by simpa [qqFvar] using hc)
      apply tau_mono le_rfl
      exact le_trans (by norm_num) (le_add_self (a := (20 : V)) (b := 20 * ^&x))
    · intro k f v hkf hv ih
      rw [termShift_func hkf hv]
      set P : V := ^func k f v
      have hk : k ≤ 2 := PA196PATermBShiftGrowth.arithmetic_arity_le_two hkf
      have hchild : ∀ i < k, termShift ℒₒᵣ v.[i] ≤ tau (P + 8) (20 * P) := by
        intro i hi
        have hi' : i < len v := by simpa [hv.lh] using hi
        have hlt : v.[i] < P := nth_lt_qqFunc_of_lt hi'
        have hdepth : 20 * v.[i] + 20 ≤ 20 * P := by
          calc 20 * v.[i] + 20 = 20 * (v.[i] + 1) := by ring
            _ ≤ 20 * P := mul_le_mul' le_rfl (lt_iff_succ_le.mp hlt)
        exact le_trans (ih i hi) (tau_mono (add_le_add (le_of_lt hlt) le_rfl) hdepth)
      have hvec : termShiftVec ℒₒᵣ k v ≤ repeatVec (tau (P + 8) (20 * P)) k := by
        have hh := len_repeatVec_of_nth_le (v := termShiftVec ℒₒᵣ k v)
          (m := tau (P + 8) (20 * P)) (fun i hi => by
            have hi' : i < k := by simpa [len_termShiftVec hv] using hi
            rw [nth_termShiftVec hv hi']
            exact hchild i hi')
        simpa [len_termShiftVec hv] using hh
      have hvbound : termShiftVec ℒₒᵣ k v ≤ tau (P + 8) (20 * P + 4) := by
        apply le_trans hvec
        apply le_trans (repeatVec_le_tau le_rfl k)
        exact tau_mono le_rfl (add_le_add le_rfl (by
          calc 2 * k ≤ 2 * (2 : V) := mul_le_mul' le_rfl hk
            _ = 4 := by norm_num))
      have hc := code4_le_tau
        (le_tau_of P 2 (20 * P + 4) (small_le P (by norm_num)))
        (le_tau_of P k (20 * P + 4) (le_trans (arity_lt_qqFunc k f v).le le_self_add))
        (le_tau_of P f (20 * P + 4) (le_trans (func_lt_qqFunc k f v).le le_self_add)) hvbound
      apply le_trans (by simpa [qqFunc] using hc)
      apply tau_mono le_rfl
      calc 20 * P + 4 + 2 + 2 + 2 = 20 * P + 10 := by ring
        _ ≤ 20 * P + 20 := add_le_add le_rfl (by norm_num)
  · simp [termShift, Language.TermRec.Construction.result_prop_not _ _ _ ht]

theorem termShiftVec_le (k v : V) :
    termShiftVec ℒₒᵣ k v ≤ repeatVec (tau (v + 8) (20 * v + 20)) k := by
  by_cases hv : IsUTermVec ℒₒᵣ k v
  · have h := len_repeatVec_of_nth_le (v := termShiftVec ℒₒᵣ k v)
      (m := tau (v + 8) (20 * v + 20)) (fun i hi => by
        have hi' : i < k := by simpa [len_termShiftVec hv] using hi
        rw [nth_termShiftVec hv hi']
        exact le_trans (termShift_le v.[i])
          (tau_mono (add_le_add (nth_le v i) le_rfl)
            (add_le_add (mul_le_mul' le_rfl (nth_le v i)) le_rfl)))
    simpa [len_termShiftVec hv] using h
  · simp [termShiftVec, hv]

theorem relation_le (tag k r v : V) (htag : tag ≤ 1) :
    ⟪tag, k, r, termShiftVec ℒₒᵣ k v⟫ + 1 ≤
      tau (v + k + r + 8) (20 * v + 2 * k + 26) := by
  let X : V := v + k + r + 8
  let D : V := 20 * v + 20 + 2 * k
  have hX : v + 8 ≤ X := by
    dsimp [X]
    calc v + 8 ≤ v + 8 + (k + r) := le_self_add
      _ = v + k + r + 8 := by ring
  have hv : termShiftVec ℒₒᵣ k v ≤ tau X D := by
    apply le_trans (termShiftVec_le k v)
    apply le_trans (repeatVec_mono_left (tau_mono hX le_rfl) k)
    simpa [D] using (repeatVec_le_tau (le_refl (tau X (20 * v + 20))) k)
  have hk : k ≤ tau X D := le_trans (by
    dsimp [X]
    calc k ≤ v + k := le_add_self
      _ ≤ v + k + r + 8 := le_trans le_self_add le_self_add) (le_tau _ _)
  have hr : r ≤ tau X D := le_trans (by
    dsimp [X]
    exact le_trans le_add_self le_self_add) (le_tau _ _)
  have ht : tag ≤ tau X D := le_trans htag (le_trans (by norm_num) (four_le_tau _ _))
  have hc := code4_le_tau ht hk hr hv
  apply le_trans hc
  apply tau_mono le_rfl
  dsimp [D]
  exact le_of_eq (by ring)

#print axioms relation_le
#print axioms termShiftVec_le
#print axioms termShift_le
end PA196PATermShiftGrowth
