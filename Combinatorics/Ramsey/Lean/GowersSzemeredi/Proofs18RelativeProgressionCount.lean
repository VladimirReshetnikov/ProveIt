import GowersSzemeredi.Proofs18RelativeBalance

/-! Counting four-term progressions relative to a support, using uniformity
of 1_A - delta 1_S rather than ambient density. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Count all k-term progressions, including zero common difference. -/
def progressionCount {N : Nat} [NeZero N] (A : Finset (ZMod N)) (k : Nat) : Nat :=
  countWhere fun p : ZMod N × ZMod N => ∀ i : Fin k, p.2 - (i : Nat) * p.1 ∈ A

theorem progressionCount_eq_progressionAverage {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (progressionCount A k : Complex) = progressionAverage (fun _ : Fin k => indicator A) := by
  have hcount {T : Type} [Fintype T] (P : T → Prop) [DecidablePred P] :
      (countWhere P : Complex) = ∑ x : T, if P x then 1 else 0 := by
    unfold countWhere
    rw [Finset.filter_congr_decidable]
    simp
  unfold progressionCount progressionAverage
  rw [hcount, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [indicator, Finset.prod_boole]
  simp

theorem progressionCount_le_modulus_of_no_ap {N k : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hno : ¬ HasModAP A k) : progressionCount A k ≤ N := by
  unfold progressionCount countWhere
  rw [Finset.filter_congr_decidable]
  calc
    _ ≤ (Finset.univ.filter fun p : ZMod N × ZMod N => p.1 = 0).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      by_contra hr
      apply hno
      refine ⟨p.2, -p.1, bne_iff_ne.mpr (neg_ne_zero.mpr hr), ?_⟩
      intro i hi
      simpa only [mul_neg, sub_eq_add_neg] using hp ⟨i, hi⟩
    _ = N := by
      rw [show (Finset.univ.filter fun p : ZMod N × ZMod N => p.1 = 0) =
          ({0} : Finset (ZMod N)) ×ˢ Finset.univ by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, and_true]]
      simp [ZMod.card]

theorem progressionAverage_const_mul {N k : Nat} [NeZero N]
    (f : Fin k → ZMod N → Complex) (c : Complex) :
    progressionAverage (fun i x => c * f i x) = c ^ k * progressionAverage f := by
  unfold progressionAverage
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.mul_sum]

end LeanProofs.GowersSzemeredi
