import GowersSzemeredi.Proofs18GeneralRelativeCount

/-! Integer-valued k-term counts and the relative-uniform stopping rule.
Constant progressions are included in the count and explicitly removed. -/
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
  classical
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
  classical
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

/-- A real lower bound for the actual integer count. -/
theorem relative_progressionCount_lower {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hN : k ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha (k - 2)) :
    delta ^ k * progressionCount S k - k * alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 ≤
      (progressionCount A k : Real) := by
  have h := relative_progression_counting_bound hk hN A S delta alpha hAS hδ hδone hα hu
  rw [← progressionCount_eq_progressionAverage, ← progressionCount_eq_progressionAverage] at h
  have hr : |(progressionCount A k : Real) - delta ^ k * progressionCount S k| ≤
      k * alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  linarith [(abs_le.mp hr).1]

/-- A support count exceeding the error plus all possible constant
progressions forces a nonconstant progression in the original set. -/
theorem relative_uniform_hasModAP {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hN : k ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha (k - 2))
    (hcount : (N : Real) + k * alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 <
      delta ^ k * progressionCount S k) : HasModAP A k := by
  by_contra hno
  have hsmall : (progressionCount A k : Real) ≤ N := by
    exact_mod_cast progressionCount_le_modulus_of_no_ap A hno
  have hlarge := relative_progressionCount_lower hk hN A S delta alpha hAS hδ hδone hα hu
  linarith

end LeanProofs.GowersSzemeredi
