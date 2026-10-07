/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem pivots_lt_of_weighted_bound {m k : ℕ}
    (p : Fin k → Fin m) (hp : Function.Injective p)
    (w : Fin m → ℝ) (hw : ∀ i, 1 ≤ w i)
    (l : ℕ) (hl : 0 < l) (a : ℕ) (T C v : ℝ)
    (hfar : ∀ i, a ≤ i.val → T ≤ w i)
    (hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ v)
    (hupper : v ≤ C) (hlarge : C * (l : ℝ) ^ m < T) :
    ∀ i, (p i).val < a := by
  have hkm : k ≤ m := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hp
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hpow : 0 < (l : ℝ) ^ k := pow_pos hlr _
  have hprod : (∏ i, w (p i)) / (l : ℝ) ^ k ≤ C := by
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hlower.trans hupper
  have hC : 0 ≤ C := (div_nonneg
    (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hw (p i)))) hpow.le).trans hprod
  have hprodm : (∏ i, w (p i)) ≤ C * (l : ℝ) ^ m := by
    apply ((div_le_iff₀ hpow).mp hprod).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr hl) hkm
  intro j
  by_contra hj
  have hsingle : w (p j) ≤ ∏ i, w (p i) := by
    have h := Finset.prod_le_prod_of_subset_of_one_le₀
      (f := fun i => w (p i)) (Finset.subset_univ ({j} : Finset (Fin k)))
      (fun i _ => zero_le_one.trans (hw (p i))) (fun i _ _ => hw (p i))
    simpa only [Finset.prod_singleton] using h
  exact (not_le_of_gt hlarge) ((hfar (p j) (Nat.le_of_not_gt hj)).trans (hsingle.trans hprodm))

end Erdos3

end

end OAI
