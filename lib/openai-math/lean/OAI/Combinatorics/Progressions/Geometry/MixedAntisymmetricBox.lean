import OAI.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem expect_mixed_tuple {n : ℕ} {X : Type*} [Fintype X]
    (F : (Fin (n + 2) → X) → ℂ) :
    (𝔼 x, F x) = 𝔼 u : Fin n → X, 𝔼 h, 𝔼 m, F (Fin.cons h (Fin.cons m u)) := by
  simp_rw [expect_dependent_fin_cons]
  calc
    _ = 𝔼 h, 𝔼 u : Fin n → X, 𝔼 m, F (Fin.cons h (Fin.cons m u)) :=
      Finset.expect_congr rfl (fun _ _ => Finset.expect_comm _ _ _)
    _ = _ := Finset.expect_comm _ _ _

namespace NativeMultidegreeNilcharacter

theorem exists_mixed_sum_antisymmetric_box (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ j k : Fin W.outputDim, Real.exp (-((p + C) ^ C)) ≤
        (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
          W.mixedAntisymmetric j k (fun l => (x l).val))).re := by
  obtain ⟨a, _, hcorr⟩ := exists_mixed_sum_antisymmetric_correlation n
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.C (2 ^ (n + 2)) * Q)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hinput
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨j, k, B, hB, hBind, hpositive⟩ := hcorr W f hf i A hA hmiss hinput
  let F (x : Fin (n + 2) → ZMod N) := W.mixedAntisymmetric j k (fun l => (x l).val)
  let U (l : Fin (n + 2)) (x : Fin (n + 2) → ZMod N) := B l (fun l => (x l).val)
  have hvals (h m : ZMod N) (u : Fin n → ZMod N) :
      (fun l => (((Fin.cons h (Fin.cons m u) : Fin (n + 2) → ZMod N) l).val : ℤ)) =
        Fin.cons (h.val : ℤ) (Fin.cons (m.val : ℤ) (fun l => (u l).val)) := by
    funext l
    refine Fin.cases ?_ (fun l => ?_) l
    · rfl
    · refine Fin.cases ?_ (fun l => ?_) l <;> rfl
  have hmean : boxTestCorrelation F U =
      𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        W.mixedAntisymmetric j k (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
          ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val))) := by
    rw [boxTestCorrelation, expect_mixed_tuple]
    simp only [F, U, hvals]
  have hU : ∀ l, MissesBoxCoordinate (U l) l := by
    intro l x v
    apply hBind l
    intro m hml
    change (((Function.update x l v) m).val : ℤ) = ((x m).val : ℤ)
    rw [Function.update_of_ne hml]
  have hbox := boxTest_cauchySchwarz (n + 1) F U (fun l x => hB l _) hU
  have hscore : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) ≤
      (boxPhaseMoment (n + 2) F).re := by
    have hpower : Real.exp (-((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a)) =
        Real.exp (-((p + a) ^ a)) ^ (2 ^ (n + 2)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hpower]
    apply (pow_le_pow_left₀ (Real.exp_nonneg _) ?_ _).trans hbox
    rwa [hmean]
  have hcost : ((2 ^ (n + 2) : ℕ) : ℝ) * ((p + a) ^ a) ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨j, k, ?_⟩
  exact (Real.exp_le_exp.mpr (by linarith)).trans hscore

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
