/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.QuarticSurvivorMultilinearization

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def quarticReflectionSource {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (c : ℤ) (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  W.eval a.1 (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]) *
    star (W.eval a.2 (quarticInput (x 1) ![c - x 0 - x 1, x 2, x 3]))

noncomputable def quarticReflectionTarget {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (x : Fin 4 → ℤ) : ℂ :=
  W.eval a.1.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]) *
    star (W.eval a.2.1 (quarticInput (x 1) ![c - x 1, x 2, x 3])) *
    star (W.eval a.1.2 (quarticInput (x 0) ![x 1, x 2, x 3])) *
    W.eval a.2.2 (quarticInput (x 1) ![x 0, x 2, x 3])

theorem exists_quartic_reflected_factor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 4 → ℤ) => W.eval i (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]))
        (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval a.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]) *
            star (W.eval a.2 (quarticInput (x 0) ![x 1, x 2, x 3]))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence (fun _ : QuarticReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hdegree : (∑ _ : QuarticReplicatedIndex, 1) - 1 = 3 := by
    have hc : Fintype.card QuarticReplicatedIndex = 4 := replicatedMixed_card 3
    simp only [Finset.sum_const, Finset.card_univ, hc]
    norm_num
  have E := (hadd W (quarticReplica 0) rfl).affinePullback
    quarticReflectionMatrix (quarticReflectionOffset c)
  have E' : NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
      (fun i (x : Fin 4 → ℤ) => W.eval i (quarticInput (x 0) ![c - x 0, x 2, x 3]))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]) *
          W.eval a.2 (quarticInput (x 0) ![x 1, x 2, x 3])) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector, quarticReflectionInput_sum,
      quarticReflectionInput_left, quarticReflectionInput_right] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i a
  obtain ⟨R⟩ := E'.symm.expansion (i, a.2) a.1
  have heq : (fun x : Fin 4 → ℤ =>
      (W.eval i (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]) *
        W.eval a.2 (quarticInput (x 0) ![x 1, x 2, x 3])) *
          star (W.eval a.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]))) =
      (fun x => W.eval i (quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3]) *
        star (W.eval a.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]) *
          star (W.eval a.2 (quarticInput (x 0) ![x 1, x 2, x 3])))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_quartic_reflected_pair_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (W.quarticReflectionSource c) (W.quarticReflectionTarget c) := by
  obtain ⟨a, _, hfactor⟩ := exists_quartic_reflected_factor_equivalence
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have E := hfactor W c
  have F := (E.coordinatePullback (![1, 0, 2, 3] : Fin 4 → Fin 4)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hsub (x : Fin 4 → ℤ) : c - x 1 - x 0 = c - x 0 - x 1 := by abel
  unfold quarticReflectionSource quarticReflectionTarget
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    hsub, star_mul, star_star, mul_assoc, mul_comm, mul_left_comm] using R.mono hcost

theorem quartic_reflection_target_unit {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (c : ℤ) (x : Fin 4 → ℤ) :
    (∑ a, ‖W.quarticReflectionTarget c a x‖ ^ 2) = 1 := by
  have heq (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)) :
      W.quarticReflectionTarget c a x =
        (W.eval a.1.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]) *
          star (W.eval a.1.2 (quarticInput (x 0) ![x 1, x 2, x 3]))) *
        star (W.eval a.2.1 (quarticInput (x 1) ![c - x 1, x 2, x 3]) *
          star (W.eval a.2.2 (quarticInput (x 1) ![x 0, x 2, x 3]))) := by
    simp only [quarticReflectionTarget, star_mul, star_star]
    ring
  simp only [heq, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, W.unit_eval, mul_one]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def NativeMultidegreeNilcharacter.quarticAntisymmetric {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
    (i j : Fin W.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  W.eval i (quarticInput (x 0) ![x 1, x 2, x 3]) *
    star (W.eval j (quarticInput (x 1) ![x 0, x 2, x 3]))

theorem exists_quartic_antisymmetric_transfer :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (c : ℤ) (i j : Fin W.outputDim) {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (sample : Ω → Fin 4 → ℤ) (A : Fin 4 → (Fin 4 → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S,
        star (W.quarticReflectionSource c (i, j) (sample u)) * ∏ k, A k (sample u)‖ →
      ∃ (i' j' : Fin W.outputDim) (B : Fin 4 → (Fin 4 → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → B i x = B i y) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S,
          W.quarticAntisymmetric i' j' (sample u) * ∏ k, B k (sample u)‖ := by
  obtain ⟨e, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_quartic_reflected_pair_equivalence
  obtain ⟨d, _, habsorb⟩ := exists_absorb_missing_coordinate_error 3
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C e) ^ e
  let R := X + 2 * Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C d) ^ d)
  refine ⟨C, hC, ?_⟩
  intro p W c i j Ω S hS sample A hA hAind hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + e) ^ e
  let r := p + 2 * q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hpr : p + 2 * q ≤ r := by dsimp only [r]; linarith
  let E := hcompare W c
  obtain ⟨k, l, htransfer⟩ := E.transfer_sample_correlation S sample (i, j)
    (fun u => ∏ a, A a (sample u))
    (fun u _ => W.quartic_reflection_target_unit c (sample u)) (by
      simpa only [mul_comm] using hcorr)
  let T := (E.selectedExpansion (i, j) k).test l
  let B (a : Fin 4) (x : Fin 4 → ℤ) :=
    if a = 0 then A a x * W.eval k.2.1 (quarticInput (x 1) ![c - x 1, x 2, x 3])
    else if a = 1 then A a x * star (W.eval k.1.1 (quarticInput (x 0) ![c - x 0, x 2, x 3]))
    else A a x
  have hB : ∀ a x, ‖B a x‖ ≤ 1 := by
    intro a x
    by_cases h0 : a = 0
    · simp only [B, h0, ite_true, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hA _ _)).trans (W.norm_eval _ _)
    · by_cases h1 : a = 1
      · subst a
        simp only [B, show (1 : Fin 4) ≠ 0 by decide, ite_false, ite_true, norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hA _ _)).trans (W.norm_eval _ _)
      · simpa only [B, h0, h1, ite_false] using hA a x
  have hBind : ∀ a x y, (∀ k, k ≠ a → x k = y k) → B a x = B a y := by
    intro a x y hxy
    by_cases h0 : a = 0
    · subst a
      simp only [B, ite_true]
      rw [hAind 0 x y hxy, hxy 1 (by decide), hxy 2 (by decide), hxy 3 (by decide)]
    · by_cases h1 : a = 1
      · subst a
        simp only [B, show (1 : Fin 4) ≠ 0 by decide, ite_false, ite_true]
        rw [hAind 1 x y hxy, hxy 0 (by decide), hxy 2 (by decide), hxy 3 (by decide)]
      · simpa only [B, h0, h1, ite_false] using hAind a x y hxy
  let F (u : Ω) := W.quarticAntisymmetric k.1.2 k.2.2 (sample u) * ∏ a, B a (sample u)
  have hF : ∀ u, ‖F u‖ ≤ 1 := by
    intro u
    dsimp only [F, NativeMultidegreeNilcharacter.quarticAntisymmetric]
    rw [norm_mul, norm_mul, norm_star, norm_prod]
    exact (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _))).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun a _ => hB a _))
  have hT : T.ComplexityLE r := ((E.selectedExpansion (i, j) k).complexity l).mono hqr
  have hpoint (u : Ω) :
      (∏ a, A a (sample u)) * star (W.quarticReflectionTarget c k (sample u)) = F u := by
    simp only [F, B, NativeMultidegreeNilcharacter.quarticAntisymmetric,
      NativeMultidegreeNilcharacter.quarticReflectionTarget, Fin.prod_univ_four,
      show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 0 by decide,
      show (3 : Fin 4) ≠ 1 by decide, ite_true, ite_false, star_mul, star_star]
    ring
  have hFcorr : Real.exp (-r) ≤ ‖𝔼 u ∈ S, F u * star (T.eval (sample u))‖ := by
    change Real.exp (-(p + 2 * q)) ≤ ‖𝔼 u ∈ S,
      ((∏ a, A a (sample u)) * star (W.quarticReflectionTarget c k (sample u))) *
        star (T.eval (sample u))‖ at htransfer
    simpa only [hpoint] using (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans htransfer
  obtain ⟨D, hD, hDind, H, _, hH, _, hfinal⟩ := habsorb T hT
    (Finset.univ : Finset Unit) Finset.univ_nonempty (fun _ => S) (fun _ _ => hS)
    (fun _ => sample) (fun _ => F) (fun _ _ u _ => hF u) (fun _ _ => hFcorr)
  obtain ⟨u, hu⟩ := hH
  have hcost : (r + d) ^ d ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, (fun a x => B a x * D a x), ?_, ?_, ?_⟩
  · intro a x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB _ _)).trans (hD _ _)
  · intro a x y hxy
    change B a x * D a x = B a y * D a y
    rw [hBind a x y hxy, hDind a x y hxy]
  · simpa only [F, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfinal u hu)

end Erdos3

end

end OAI
