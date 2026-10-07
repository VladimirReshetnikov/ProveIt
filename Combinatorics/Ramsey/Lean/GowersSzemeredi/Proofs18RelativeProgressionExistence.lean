import GowersSzemeredi.Proofs18RelativeProgressionCount

/-! Integer-valued four-term counts and the relative-uniform stopping rule.
Constant progressions are included in the count and explicitly removed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Count all four-term progressions, including zero common difference. -/
def fourTermCount {N : Nat} [NeZero N] (A : Finset (ZMod N)) : Nat :=
  countWhere fun p : ZMod N × ZMod N => ∀ i : Fin 4, p.2 - (i : Nat) * p.1 ∈ A

theorem fourTermCount_eq_progressionAverage {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (fourTermCount A : Complex) = progressionAverage (fun _ : Fin 4 => indicator A) := by
  classical
  have hcount {T : Type} [Fintype T] (P : T → Prop) [DecidablePred P] :
      (countWhere P : Complex) = ∑ x : T, if P x then 1 else 0 := by
    unfold countWhere
    rw [Finset.filter_congr_decidable]
    simp
  unfold fourTermCount progressionAverage
  rw [hcount, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [indicator, Finset.prod_boole]
  simp

theorem fourTermCount_le_modulus_of_no_ap {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hno : ¬ HasModAP A 4) : fourTermCount A ≤ N := by
  classical
  unfold fourTermCount countWhere
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
theorem relative_fourTermCount_lower {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2) :
    delta ^ 4 * fourTermCount S - 4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 ≤
      (fourTermCount A : Real) := by
  have h := relative_fourFactor_counting_bound hN A S delta alpha hAS hδ hδone hα hu
  rw [← fourTermCount_eq_progressionAverage, ← fourTermCount_eq_progressionAverage] at h
  have hr : |(fourTermCount A : Real) - delta ^ 4 * fourTermCount S| ≤
      4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  linarith [(abs_le.mp hr).1]

/-- A support count exceeding the error plus all possible constant
progressions forces a nonconstant progression in the original set. -/
theorem relative_uniform_hasModAP_four {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2)
    (hcount : (N : Real) + 4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 <
      delta ^ 4 * fourTermCount S) : HasModAP A 4 := by
  by_contra hno
  have hsmall : (fourTermCount A : Real) ≤ N := by
    exact_mod_cast fourTermCount_le_modulus_of_no_ap A hno
  have hlarge := relative_fourTermCount_lower hN A S delta alpha hAS hδ hδone hα hu
  linarith

end LeanProofs.GowersSzemeredi
