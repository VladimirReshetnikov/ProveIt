import PA196PASubstitutionTotalGrowth
import PA196PASubstitutionConstructorGrowth
import PA196InductionImpGrowth

/-! A tower bound for the exact induction-body value function in all IΣ₁
models, including malformed inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196InductionBodyGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA196PAQVecTowerAlgebra PA196PASubstitutionTotalGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem step_eq (B : V) : iter 1 B = tau (B+8) (22*B+22) := by
  simpa using iter_succ (0:V) B

theorem imp_le_step {a b B : V} (ha : a ≤ B) (hb : b ≤ B) :
    imp ℒₒᵣ a b ≤ iter 1 B := by
  rw [step_eq]
  apply le_trans (PA196InductionImpGrowth.imp_all ha hb)
  apply tau_mono le_rfl
  exact add_le_add (mul_le_mul' (by norm_num : (2:V) ≤ 22) le_rfl) (by norm_num)

theorem all_le_step {a B : V} (ha : a ≤ B) : ^∀ a ≤ iter 1 B := by
  rw [step_eq]
  exact PA196PASubstitutionConstructorGrowth.all_le B a ha

theorem body_le_tower (k : V) :
    indBodyVal k ≤ iter (k + (indSubstConst0:V) + (indSubstConst1:V) + 6)
      (4*(k + (indSubstConst0:V) + (indSubstConst1:V)) + 1) := by
  let c0 : V := indSubstConst0
  let c1 : V := indSubstConst1
  let X : V := k + c0 + c1
  let B : V := iter (X+2) (4*X+1)
  have hX0 : k+c0 ≤ X := le_self_add
  have hX1 : k+c1 ≤ X := by
    change k+c1 ≤ k+c0+c1
    calc
      k+c1 ≤ (k+c1)+c0 := le_self_add
      _ = k+c0+c1 := by ring
  have hkX : k ≤ X := le_trans le_self_add le_self_add
  have hkB : k ≤ B := by
    apply le_trans hkX
    apply le_trans ?_ (iter_inflationary _ _)
    calc
      X ≤ X+(X+X+X)+1 := le_trans le_self_add le_self_add
      _ = 4*X+1 := by ring
  have hs0 : subst ℒₒᵣ c0 k ≤ B := by
    apply le_trans (subst_le_tower c0 k)
    exact le_trans (iter_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl hX0) le_rfl))
      (iter_index_mono _ _ _ (add_le_add hX0 le_rfl))
  have hs1 : subst ℒₒᵣ c1 k ≤ B := by
    apply le_trans (subst_le_tower c1 k)
    exact le_trans (iter_seed_mono _ _ _ (add_le_add (mul_le_mul' le_rfl hX1) le_rfl))
      (iter_index_mono _ _ _ (add_le_add hX1 le_rfl))
  have hi1 : imp ℒₒᵣ k (subst ℒₒᵣ c1 k) ≤ iter 1 B := imp_le_step hkB hs1
  have hqa1 : ^∀ (imp ℒₒᵣ k (subst ℒₒᵣ c1 k)) ≤ iter 1 (iter 1 B) := all_le_step hi1
  have hqak : ^∀ k ≤ iter 1 (iter 1 B) := by
    exact le_trans (all_le_step hkB) (iter_inflationary 1 (iter 1 B))
  have hi2 : imp ℒₒᵣ (^∀ (imp ℒₒᵣ k (subst ℒₒᵣ c1 k))) (^∀ k) ≤
      iter 1 (iter 1 (iter 1 B)) := imp_le_step hqa1 hqak
  have ha : subst ℒₒᵣ c0 k ≤ iter 1 (iter 1 (iter 1 B)) := by
    exact le_trans hs0 (le_trans (iter_inflationary 1 B)
      (le_trans (iter_inflationary 1 (iter 1 B)) (iter_inflationary 1 (iter 1 (iter 1 B)))))
  have hy := imp_le_step ha hi2
  have hiter : iter 1 (iter 1 (iter 1 (iter 1 B))) = iter (X+6) (4*X+1) := by
    dsimp only [B]
    rw [←iter_add, ←iter_add, ←iter_add, ←iter_add]
    congr 1; ring
  rw [hiter] at hy
  unfold indBodyVal
  rw [←val_indSubstConst0, ←val_indSubstConst1]
  simpa [c0, c1, X] using hy

#print axioms body_le_tower
end PA196InductionBodyGrowth
