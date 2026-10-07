import OAI.Combinatorics.Progressions.Estimates.LieFiniteProduct

namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

def lieTreeSupport : FreeMagma I → Set I
  | .of i => {i}
  | .mul a b => lieTreeSupport a ∪ lieTreeSupport b

theorem lieTreeEval_congr_on (v w : I → L) (a : FreeMagma I)
    (h : ∀ i ∈ lieTreeSupport a, v i = w i) : lieTreeEval v a = lieTreeEval w a := by
  induction a using FreeMagma.rec with
  | of i => exact h i (Set.mem_singleton i)
  | mul a b ha hb =>
    exact congrArg₂ (fun x y : L => ⁅x, y⁆)
      (ha (fun i hi => h i (Or.inl hi))) (hb (fun i hi => h i (Or.inr hi)))

theorem lieTreeEval_eq_zero_of_leaf (v : I → L) (a : FreeMagma I) {i : I}
    (hi : i ∈ lieTreeSupport a) (hv : v i = 0) : lieTreeEval v a = 0 := by
  induction a using FreeMagma.rec with
  | of j =>
    have hij : i = j := hi
    simpa only [lieTreeEval, ← hij] using hv
  | mul a b ha hb =>
    rcases hi with hi | hi
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [ha hi, zero_lie]
    · change ⁅lieTreeEval v a, lieTreeEval v b⁆ = 0
      rw [hb hi, lie_zero]

theorem lieTreeEval_pi (v : I → J → L) (a : FreeMagma I) (j : J) :
    lieTreeEval v a j = lieTreeEval (fun i => v i j) a := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    change ⁅lieTreeEval v a j, lieTreeEval v b j⁆ =
      ⁅lieTreeEval (fun i => v i j) a, lieTreeEval (fun i => v i j) b⁆
    rw [ha, hb]

end Erdos3

end

end OAI
