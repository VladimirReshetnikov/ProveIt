import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def SquarefreeExponent {ι : Type*} (a : ι →₀ ℕ) : Prop := ∀ i, a i ≤ 1

abbrev SquarefreeIndex (ι : Type*) := {a : ι →₀ ℕ // SquarefreeExponent a}

theorem not_squarefreeExponent_add_right {ι : Type*} (a b : ι →₀ ℕ)
    (hb : ¬SquarefreeExponent b) : ¬SquarefreeExponent (a + b) := by
  intro h
  apply hb
  intro i
  have hi : a i + b i ≤ 1 := h i
  omega

theorem squarefreeExponent_add_iff {ι : Type*} (a b : ι →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) :
    SquarefreeExponent (a + b) ↔ Disjoint a.support b.support := by
  classical
  rw [Finset.disjoint_left]
  constructor
  · intro h i hi hj
    have hsum : a i + b i ≤ 1 := h i
    have hai := Finsupp.mem_support_iff.mp hi
    have hbi := Finsupp.mem_support_iff.mp hj
    omega
  · intro h i
    have hai := ha i
    have hbi := hb i
    change a i + b i ≤ 1
    by_cases hzero : a i = 0
    · omega
    · have hz : b i = 0 := by
        by_contra hn
        exact h (Finsupp.mem_support_iff.mpr hzero) (Finsupp.mem_support_iff.mpr hn)
      omega

noncomputable def squarefreeIndexEquiv (ι : Type*) [Fintype ι] :
    SquarefreeIndex ι ≃ (ι → Fin 2) where
  toFun a i := ⟨a.val i, Nat.lt_succ_of_le (a.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val),
    fun i => Nat.le_of_lt_succ (f i).isLt⟩
  left_inv _ := Subtype.ext (Finsupp.ext fun _ => rfl)
  right_inv _ := funext fun _ => Fin.ext rfl

noncomputable instance squarefreeIndexFintype (ι : Type*) [Fintype ι] : Fintype (SquarefreeIndex ι) := by
  classical
  exact Fintype.ofEquiv (ι → Fin 2) (squarefreeIndexEquiv ι).symm

theorem card_squarefreeIndex (ι : Type*) [Fintype ι] :
    Fintype.card (SquarefreeIndex ι) = 2 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (squarefreeIndexEquiv ι), Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

end OAI
