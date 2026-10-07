/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CyclicMixedReflection
import OAI.Combinatorics.Progressions.Estimates.MixedPermutationTensor

namespace OAI

section

namespace Erdos3

def mixedSlotInput {n : ℕ} {α : Type*} (h t : α) (v : Fin n → α) :
    MixedReplicatedIndex (n + 1) → α := mixedReplicatedInput h (Fin.cons t v)

theorem mixedSlotInput_update {n : ℕ} {α : Type*} (h t u : α) (v : Fin n → α) :
    Function.update (mixedSlotInput h t v) (mixedReplica 0) u = mixedSlotInput h u v := by
  classical
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · have hne : mixedHead (n + 1) ≠ mixedReplica (0 : Fin (n + 1)) := by
      intro heq
      have hf := congrArg (fun a : MixedReplicatedIndex (n + 1) => a.1) heq
      norm_num [mixedHead, mixedReplica] at hf
    simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Function.update_self, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_zero]
    · have hne : mixedReplica i.succ ≠ mixedReplica (0 : Fin (n + 1)) :=
        fun heq => Fin.succ_ne_zero i (mixedReplica_injective (n + 1) heq)
      simp only [Function.update_of_ne hne, mixedSlotInput, mixedReplicatedInput_replica, Fin.cons_succ]

def mixedExchangeCoordinate (n : ℕ) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ))

def mixedReflectionLinear (n : ℕ) (j : Option (MixedReplicatedIndex (n + 1))) :
    (Fin (n + 2) → ℤ) →+ ℤ :=
  let ev (i : Fin (n + 2)) : (Fin (n + 2) → ℤ) →+ ℤ :=
    ⟨⟨fun x => x i, rfl⟩, fun _ _ => rfl⟩
  match j with
  | none => ev 1
  | some a => mixedSlotInput (ev 0) (-ev 0 - ev 1) (fun i => ev i.succ.succ) a

def mixedReflectionOffset (n : ℕ) (c : ℤ) : Option (MixedReplicatedIndex (n + 1)) → ℤ
  | none => 0
  | some j => mixedSlotInput 0 c (fun _ : Fin n => 0) j

def mixedReflectionAffineInput (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : Option (MixedReplicatedIndex (n + 1))) : ℤ :=
  mixedReflectionOffset n c j + mixedReflectionLinear n j x

theorem mixedReflectionAffineInput_none (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    mixedReflectionAffineInput n c x none = x 1 := by
  simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear]

theorem mixedReflectionAffineInput_some (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ)
    (j : MixedReplicatedIndex (n + 1)) :
    mixedReflectionAffineInput n c x (some j) =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) j := by
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
      mixedSlotInput, mixedReplicatedInput_head]
  · refine Fin.cases ?_ (fun i => ?_) i
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica, sub_eq_add_neg, add_assoc]
    · simp [mixedReflectionAffineInput, mixedReflectionOffset, mixedReflectionLinear,
        mixedSlotInput, mixedReplicatedInput_replica]

theorem mixedReflectionInput_sum (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 0 =
      mixedSlotInput (x 0) (c - x 0) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_sum]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none]
  rw [show mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) (mixedReplica 0) =
    c - x 0 - x 1 from rfl, sub_add_cancel, mixedSlotInput_update]

theorem mixedReflectionInput_left (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 1 =
      mixedSlotInput (x 0) (c - x 0 - x 1) (fun i => x i.succ.succ) := by
  funext j
  exact mixedReflectionAffineInput_some n c x j

theorem mixedReflectionInput_right (n : ℕ) (c : ℤ) (x : Fin (n + 2) → ℤ) :
    coordinateAdditionInputs (mixedReplica 0) (mixedReflectionAffineInput n c x) 2 =
      mixedSlotInput (x 0) (x 1) (fun i => x i.succ.succ) := by
  rw [coordinateAdditionInputs_right]
  simp only [mixedReflectionAffineInput_some, mixedReflectionAffineInput_none, mixedSlotInput_update]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_separated_sample_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {J K : Type*} [Fintype J] [Fintype K]
        {chi : J → (Fin (s + 1) → ℤ) → ℂ} {eta : K → (Fin (s + 1) → ℤ) → ℂ},
      NativeIntegerVectorEquivalence s p chi eta →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) →
      ∀ {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (sample : Ω → Fin (s + 1) → ℤ) (f : Ω → ℂ),
      (∀ u ∈ S, ‖f u‖ ≤ 1) →
      ∀ (j : J) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S, f u * star (chi j (sample u)) * ∏ i, A i (sample u)‖ →
      ∃ (k : K) (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 u ∈ S, f u * star (eta k (sample u)) * ∏ i, B i (sample u)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * X + 2 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp J K _ _ chi eta E hunit Ω S hS sample f hf j A hA hAind hcorr
  classical
  have heta (k : K) (x : Fin (s + 1) → ℤ) : ‖eta k x‖ ≤ 1 := by
    have hle : ‖eta k x‖ ^ 2 ≤ ∑ l, ‖eta l x‖ ^ 2 :=
      Finset.single_le_sum (fun l _ => sq_nonneg ‖eta l x‖) (Finset.mem_univ k)
    rw [hunit] at hle
    nlinarith only [hle, norm_nonneg (eta k x)]
  obtain ⟨k, l, htransfer⟩ := E.transfer_sample_correlation S sample j
    (fun u => f u * ∏ i, A i (sample u)) (fun u _ => hunit (sample u)) (by
      simpa only [mul_right_comm] using hcorr)
  let T := (E.selectedExpansion j k).test l
  let r := 3 * p + 2
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have h3pr : p + 2 * p ≤ r := by dsimp only [r]; linarith
  let F (u : Ω) := f u * star (eta k (sample u)) * ∏ i, A i (sample u)
  have hF : ∀ u ∈ S, ‖F u‖ ≤ 1 := by
    intro u hu
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_star, norm_prod]
    exact (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (hf u hu)).trans (heta k _))).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA i _))
  have hT : T.ComplexityLE r := ((E.selectedExpansion j k).complexity l).mono hpr
  have hFcorr : Real.exp (-r) ≤ ‖𝔼 u ∈ S, F u * star (T.eval (sample u))‖ := by
    simpa only [F, T, mul_right_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg h3pr)).trans htransfer
  obtain ⟨D, hD, hDind, H, _, hH, _, hfinal⟩ := habsorb T hT
    (Finset.univ : Finset Unit) Finset.univ_nonempty (fun _ => S) (fun _ _ => hS)
    (fun _ => sample) (fun _ => F) (fun _ _ u hu => hF u hu) (fun _ _ => hFcorr)
  obtain ⟨u, hu⟩ := hH
  have hcost : (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k, (fun i x => A i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hD i x)
  · intro i x y hxy
    change A i x * D i x = A i y * D i y
    rw [hAind i x y hxy, hDind i x y hxy]
  · simpa only [F, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfinal u hu)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedReflectionSource {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : Fin W.outputDim × Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
    star (W.eval a.2 (mixedSlotInput (x 1) (c - x 0 - x 1) (fun j => x j.succ.succ)))

noncomputable def mixedReflectionTarget {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
    star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ))) *
    star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
    W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ))

theorem exists_mixed_reflected_factor_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (fun i (x : Fin (n + 2) → ℤ) => W.eval i
          (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)))
        (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
            star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence
    (fun _ : MixedReplicatedIndex (n + 1) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W c
  have hdegree : (∑ _ : MixedReplicatedIndex (n + 1), 1) - 1 = n + 1 := by
    have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
    simp only [Finset.sum_const, Finset.card_univ, hc, smul_eq_mul, mul_one]
    omega
  have E := (hadd W (mixedReplica 0) rfl).affinePullbackHom
    (mixedReflectionLinear n) (mixedReflectionOffset n c)
  have hinput (x : Fin (n + 2) → ℤ) :
      (fun j => mixedReflectionOffset n c j + mixedReflectionLinear n j x) =
        mixedReflectionAffineInput n c x := rfl
  have E' : NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
      (fun i (x : Fin (n + 2) → ℤ) => W.eval i
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))
      (fun a : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval a.1 (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector,
      hinput, mixedReflectionInput_sum,
      mixedReflectionInput_left, mixedReflectionInput_right] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i a
  obtain ⟨R⟩ := E'.symm.expansion (i, a.2) a.1
  have heq :
      (fun x : Fin (n + 2) → ℤ =>
        (W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
          W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))) *
            star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) =
      (fun x => W.eval i (mixedSlotInput (x 0) (c - x 0 - x 1) (fun j => x j.succ.succ)) *
        star (W.eval a.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_mixed_reflected_pair_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p) (c : ℤ),
      NativeIntegerVectorEquivalence (n + 1) ((p + C) ^ C)
        (W.mixedReflectionSource c) (W.mixedReflectionTarget c) := by
  obtain ⟨a, _, hfactor⟩ := exists_mixed_reflected_factor_equivalence n
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
  have F := (E.coordinatePullback (mixedExchangeCoordinate n)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (i : Fin n) : mixedExchangeCoordinate n i.succ.succ = i.succ.succ := rfl
  have hsub (x : Fin (n + 2) → ℤ) : c - x 1 - x 0 = c - x 0 - x 1 := by abel
  unfold mixedReflectionSource mixedReflectionTarget
  simpa only [h0, h1, ht, hsub, star_mul, star_star, mul_assoc, mul_comm, mul_left_comm]
    using R.mono hcost

theorem mixed_reflection_target_unit {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (x : Fin (n + 2) → ℤ) :
    ∑ a, ‖W.mixedReflectionTarget c a x‖ ^ 2 = 1 := by
  have heq (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim)) :
      W.mixedReflectionTarget c a x =
        (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)) *
          star (W.eval a.1.2 (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)))) *
        star (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) *
          star (W.eval a.2.2 (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))) := by
    simp only [mixedReflectionTarget, star_mul, star_star]
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

theorem exists_separated_family_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ {J K : Type*} [Fintype J] [Fintype K]
        {chi : J → (Fin (s + 1) → ℤ) → ℂ} {eta : K → (Fin (s + 1) → ℤ) → ℂ},
      NativeIntegerVectorEquivalence s p chi eta →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) →
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (s + 1) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (j : J) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 u ∈ S h, f h u * star (chi j (sample h u)) * ∏ i, A i (sample h u)‖) →
      ∃ (k : K) (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * star (eta k (sample h u)) * ∏ i, B i (sample h u)‖ := by
  obtain ⟨a, _, habsorb⟩ := exists_absorb_missing_coordinate_error s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (3 * X + 2 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp J K _ _ chi eta E hunit G Ω H hH S hS sample f hf j A hA hAind hcorr
  classical
  let P := Σ k : K, Fin (E.selectedExpansion j k).count
  let rel (h : G) (_ : Unit) (c : P) : Prop :=
    Real.exp (-(p + 2 * p)) ≤ ‖𝔼 u ∈ S h,
      (f h u * ∏ i, A i (sample h u)) * star (eta c.1 (sample h u)) *
        star (((E.selectedExpansion j c.1).test c.2).eval (sample h u))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, l, hl⟩ := E.transfer_sample_correlation (S h) (sample h) j
      (fun u => f h u * ∏ i, A i (sample h u)) (fun u _ => hunit (sample h u)) (by
        simpa only [mul_right_comm] using hcorr h hh)
    exact ⟨⟨k, l⟩, hl⟩
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p) := by
    change (Fintype.card (Σ k : K, Fin (E.selectedExpansion j k).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _k : K, Real.exp p := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [Fintype.card_fin] using (E.selectedExpansion j k).count_bound
      _ = (Fintype.card K : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, two_mul]
  obtain ⟨c, H₁, hsub₁, hH₁, hsize₁, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  have hsize₁' : Real.exp (-(2 * p)) * (H.card : ℝ) ≤ (H₁.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize₁
  let T := (E.selectedExpansion j (c ()).1).test (c ()).2
  let r := 3 * p + 2
  let t := (r + a) ^ a
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have h3pr : p + 2 * p ≤ r := by dsimp only [r]; linarith
  have htotal : 2 * p + t ≤ (p + C) ^ C := by
    simpa [X, r, t, Polynomial.eval₂_pow] using hbudget p hp
  have htc : t ≤ (p + C) ^ C := by linarith
  have heta (x : Fin (s + 1) → ℤ) : ‖eta (c ()).1 x‖ ≤ 1 := by
    have hle : ‖eta (c ()).1 x‖ ^ 2 ≤ ∑ k, ‖eta k x‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg ‖eta k x‖) (Finset.mem_univ _)
    rw [hunit] at hle
    nlinarith only [hle, norm_nonneg (eta (c ()).1 x)]
  let F (h : G) (u : Ω) := f h u * star (eta (c ()).1 (sample h u)) * ∏ i, A i (sample h u)
  have hF : ∀ h ∈ H₁, ∀ u ∈ S h, ‖F h u‖ ≤ 1 := by
    intro h hh u hu
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_star, norm_prod]
    exact (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      ((mul_le_of_le_one_left (norm_nonneg _) (hf h (hsub₁ hh) u hu)).trans (heta _))).trans
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hA i _))
  have hFcorr : ∀ h ∈ H₁, Real.exp (-r) ≤
      ‖𝔼 u ∈ S h, F h u * star (T.eval (sample h u))‖ := by
    intro h hh
    have ht := hfixed h hh ()
    dsimp only [rel] at ht
    simpa only [F, T, mul_right_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg h3pr)).trans ht
  obtain ⟨D, hD, hDind, H₂, hsub₂, hH₂, hsize₂, hfinal⟩ := habsorb T
    (((E.selectedExpansion j (c ()).1).complexity (c ()).2).mono hpr)
    H₁ hH₁ S (fun h hh => hS h (hsub₁ hh)) sample F hF hFcorr
  refine ⟨(c ()).1, (fun i x => A i x * D i x), ?_, ?_, H₂, hsub₂.trans hsub₁, hH₂, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA i x)).trans (hD i x)
  · intro i x y hxy
    change A i x * D i x = A i y * D i y
    rw [hAind i x y hxy, hDind i x y hxy]
  · calc
      _ ≤ Real.exp (-(2 * p + t)) * (H.card : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (Nat.cast_nonneg _)
      _ = Real.exp (-t) * (Real.exp (-(2 * p)) * (H.card : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-t) * (H₁.card : ℝ) :=
        mul_le_mul_of_nonneg_left hsize₁' (Real.exp_nonneg _)
      _ ≤ _ := hsize₂
  · intro h hh
    simpa only [F, Finset.prod_mul_distrib, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg htc)).trans (hfinal h hh)

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedAntisymmetric {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (a b : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  W.eval a (mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ)) *
    star (W.eval b (mixedSlotInput (x 1) (x 0) (fun j => x j.succ.succ)))

theorem exists_mixed_reflection_weights {n : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
    (c : ℤ) (a : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim))
    (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ)
    (hB : ∀ i x, ‖B i x‖ ≤ 1)
    (hBind : ∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) :
    ∃ C : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ,
      (∀ i x, ‖C i x‖ ≤ 1) ∧
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → C i x = C i y) ∧
      ∀ x, star (W.mixedReflectionTarget c a x) * (∏ i, B i x) =
        W.mixedAntisymmetric a.1.2 a.2.2 x * ∏ i, C i x := by
  classical
  let F (i : Fin 2) (x : Fin (n + 2) → ℤ) : ℂ :=
    Fin.cases
      (W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)))
      (fun _ => star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ)))) i
  have hF0 (x : Fin (n + 2) → ℤ) : F 0 x =
      W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) (fun j => x j.succ.succ)) := rfl
  have hF1 (x : Fin (n + 2) → ℤ) : F 1 x =
      star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))) := rfl
  have hF : ∀ i x, ‖F i x‖ ≤ 1 := by
    intro i x
    fin_cases i
    · exact W.norm_eval _ _
    · change ‖F 1 x‖ ≤ 1
      simpa only [hF1, norm_star] using W.norm_eval a.1.1
        (mixedSlotInput (x 0) (c - x 0) (fun j => x j.succ.succ))
  have hFind : ∀ i, ∃ k : Fin (n + 2), ∀ x y,
      (∀ l, l ≠ k → x l = y l) → F i x = F i y := by
    intro i
    fin_cases i
    · refine ⟨0, ?_⟩
      intro x y hxy
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (Fin.succ_ne_zero j.succ))
      change W.eval a.2.1 (mixedSlotInput (x 1) (c - x 1) _) =
        W.eval a.2.1 (mixedSlotInput (y 1) (c - y 1) _)
      rw [hxy 1 (Fin.succ_ne_zero (0 : Fin (n + 1))), ht]
    · refine ⟨1, ?_⟩
      intro x y hxy
      have hne (j : Fin n) : j.succ.succ ≠ (1 : Fin (n + 2)) := by
        intro heq
        exact Fin.succ_ne_zero j (Fin.succ_injective (n + 1) heq)
      have ht : (fun j : Fin n => x j.succ.succ) = fun j => y j.succ.succ :=
        funext (fun j => hxy j.succ.succ (hne j))
      change star (W.eval a.1.1 (mixedSlotInput (x 0) (c - x 0) _)) =
        star (W.eval a.1.1 (mixedSlotInput (y 0) (c - y 0) _))
      rw [hxy 0 (Fin.succ_ne_zero (0 : Fin (n + 1))).symm, ht]
  obtain ⟨D, hD, hDind, hDprod⟩ := exists_missing_coordinate_product_factors F hF hFind
  refine ⟨(fun i x => B i x * D i x), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * D i x = B i y * D i y
    rw [hBind i x y hxy, hDind i x y hxy]
  · intro x
    rw [Finset.prod_mul_distrib, hDprod]
    simp only [Fin.prod_univ_two, hF0, hF1,
      mixedReflectionTarget, mixedAntisymmetric, star_mul, star_star]
    ring

theorem exists_mixed_antisymmetric_family (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (c : ℤ) (i j : Fin W.outputDim),
      ∀ {G Ω : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset Ω), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → Ω → Fin (n + 2) → ℤ) (f : G → Ω → ℂ),
      (∀ h ∈ H, ∀ u ∈ S h, ‖f h u‖ ≤ 1) →
      ∀ (A : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
      (∀ k x, ‖A k x‖ ≤ 1) →
      (∀ k x y, (∀ l, l ≠ k → x l = y l) → A k x = A k y) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 u ∈ S h,
        f h u * star (W.mixedReflectionSource c (i, j) (sample h u)) * ∏ k, A k (sample h u)‖) →
      ∃ (i' j' : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ k x, ‖B k x‖ ≤ 1) ∧
        (∀ k x y, (∀ l, l ≠ k → x l = y l) → B k x = B k y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 u ∈ S h, f h u * W.mixedAntisymmetric i' j' (sample h u) * ∏ k, B k (sample h u)‖ := by
  obtain ⟨a, _, hreflect⟩ := exists_mixed_reflected_pair_equivalence n
  obtain ⟨b, _, htransfer⟩ := exists_separated_family_correlation (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W c i j G Ω H hH S hS sample f hf A hA hAind hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E := hreflect W c
  obtain ⟨k, B, hB, hBind, H', hsub, hH', hsize, hBcorr⟩ := htransfer hr (E.mono hqr)
    (W.mixed_reflection_target_unit c) H hH S hS sample f hf (i, j) A hA hAind
    (fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hcorr h hh))
  obtain ⟨D, hD, hDind, hpoint⟩ := W.exists_mixed_reflection_weights c k B hB hBind
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, D, hD, hDind, H', hsub, hH', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg _)).trans hsize
  · intro h hh
    have heq : (𝔼 u ∈ S h, f h u * star (W.mixedReflectionTarget c k (sample h u)) *
        ∏ l, B l (sample h u)) =
        𝔼 u ∈ S h, f h u * W.mixedAntisymmetric k.1.2 k.2.2 (sample h u) * ∏ l, D l (sample h u) := by
      apply Finset.expect_congr rfl
      intro u _
      rw [mul_assoc, hpoint, ← mul_assoc]
    rw [← heq]
    exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hBcorr h hh)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_separated_correlation (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex s => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
        W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) = W.eval k x) →
      ∀ {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (sample : Ω → Fin (s + 1) → ℤ) (f : Ω → ℂ),
      (∀ u ∈ S, ‖f u‖ ≤ 1) →
      ∀ (j : Fin W.outputDim) (A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
      (∀ i x, ‖A i x‖ ≤ 1) →
      (∀ i x y, (∀ l, l ≠ i → x l = y l) → A i x = A i y) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S, f u * star (W.eval j
        (mixedReplicatedInput (sample u 0) (fun _ : Fin s => ∑ l : Fin s, sample u l.succ))) *
          ∏ i, A i (sample u)‖ →
      ∃ (a : Equiv.Perm (Fin s) → Fin W.outputDim)
        (B : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ),
        (∀ i x, ‖B i x‖ ≤ 1) ∧
        (∀ i x y, (∀ l, l ≠ i → x l = y l) → B i x = B i y) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 u ∈ S, f u * star (mixedPermutationProduct W.eval a (sample u)) *
            ∏ i, B i (sample u)‖ := by
  obtain ⟨a, _, hexpand⟩ := exists_mixed_permutation_partition_expansion s hs
  obtain ⟨b, _, htransfer⟩ := exists_separated_sample_correlation s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Q + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W hsym Ω S hS sample f hf j A hA hAind hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have E : NativeIntegerVectorEquivalence s q
      (fun i (x : Fin (s + 1) → ℤ) => W.eval i
        (mixedReplicatedInput (x 0) (fun _ : Fin s => ∑ l : Fin s, x l.succ)))
      (mixedAssignmentPartitionVector W.eval) := hexpand W hsym
  obtain ⟨k, B, hB, hBind, hBcorr⟩ := htransfer hr (E.mono hqr)
    (mixedAssignmentPartitionVector_unit W.eval W.unit_eval) S hS sample f hf j A hA hAind
    ((Real.exp_le_exp.mpr (neg_le_neg hpr)).trans hcorr)
  obtain ⟨D, hD, hDind, hDprod⟩ := W.exists_mixed_missing_factors (fun v => k (Sum.inr v))
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨(fun e => k (Sum.inl e)), (fun i x => B i x * star (D i x)), ?_, ?_, ?_⟩
  · intro i x
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB i x)).trans (hD i x)
  · intro i x y hxy
    change B i x * star (D i x) = B i y * star (D i y)
    rw [hBind i x y hxy, hDind i x y hxy]
  · simp only [Finset.prod_mul_distrib, ← star_prod, hDprod]
    simpa only [mixedAssignmentPartitionVector, star_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hBcorr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators Classical

theorem exists_mixed_sum_antisymmetric_correlation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ (j k : Fin W.outputDim) (B : Fin (n + 2) → (Fin (n + 2) → ℤ) → ℂ),
        (∀ j x, ‖B j x‖ ≤ 1) ∧
        (∀ j x y, (∀ l, l ≠ j → x l = y l) → B j x = B j y) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 u : Fin n → ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
            W.mixedAntisymmetric j k
                (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun l => (u l).val))) *
              ∏ l, B l (Fin.cons (h.val : ℤ) (Fin.cons (h'.val : ℤ) (fun j => (u j).val)))‖ := by
  obtain ⟨b, _, htransfer⟩ := exists_mixed_antisymmetric_family n
  let X : Polynomial ℕ := Polynomial.X
  let R := X + Polynomial.C (2 * 2 ^ (n + 1)) * X + 12
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := 2 * ((2 ^ (n + 1) : ℕ) : ℝ) * p + 10
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  let K (_ : Unit) (h m : ℤ) (u : Fin n → ℤ) := star (W.eval i (mixedSlotInput h m u))
  have hK : ∀ t h m u, ‖K t h m u‖ ≤ 1 := by
    intro t h m u
    simpa only [K, norm_star] using W.norm_eval i (mixedSlotInput h m u)
  obtain ⟨z, carry, D, hD, hDind, hreflect⟩ := exists_cyclic_mixed_reflection n hp K hK
    (fun _ => f) (fun _ => hf) (fun _ => A) (fun _ => hA) (fun _ => hmiss) (by
      simpa only [K, Fintype.expect_const] using hcorr)
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let V := W.mono hpr
  let sample (t : (Fin n → ZMod N) × (ZMod N × ZMod N)) : Fin (n + 2) → ℤ :=
    Fin.cons (t.2.1.val : ℤ) (Fin.cons (t.2.2.val : ℤ) (fun l => (t.1 l).val))
  have hpoint (u : Fin n → ZMod N) (h h' : ZMod N) :
      star (V.mixedReflectionSource c (i, i) (sample (u, (h, h')))) =
        K () h.val (c - h.val - h'.val) (fun l => (u l).val) *
          star (K () h'.val (c - h.val - h'.val) (fun l => (u l).val)) := by
    change star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)) *
      star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val)))) =
        star (W.eval i (mixedSlotInput (h.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))) *
          star (star (W.eval i (mixedSlotInput (h'.val : ℤ) (c - h.val - h'.val) (fun l => (u l).val))))
    simp only [star_mul, star_star]
    exact mul_comm _ _
  have hsource : Real.exp (-r) ≤
      ‖𝔼 t : (Fin n → ZMod N) × (ZMod N × ZMod N),
        star (V.mixedReflectionSource c (i, i) (sample t)) * ∏ l, D () l (sample t)‖ := by
    simp_rw [expect_prod_split, hpoint]
    simpa only [Fintype.univ_unit, Finset.expect_singleton, sample, c] using
      (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hreflect
  obtain ⟨j, k, B, hB, hBind, H, _, hH, _, hfinal⟩ := htransfer V c i i
    (Finset.univ : Finset Unit) Finset.univ_nonempty
    (fun _ => (Finset.univ : Finset ((Fin n → ZMod N) × (ZMod N × ZMod N))))
    (fun _ _ => Finset.univ_nonempty) (fun _ => sample) (fun _ _ => (1 : ℂ))
    (fun _ _ _ _ => by norm_num) (D ()) (hD ()) (hDind ())
    (fun _ _ => by simpa only [one_mul] using hsource)
  obtain ⟨t, ht⟩ := hH
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by
    convert hbudget p hp using 1
    simp [X, R, r, q, Polynomial.eval₂_pow, Nat.cast_mul]
    ring
  have hmono (x : Fin (n + 2) → ℤ) :
      V.mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  simp_rw [hmono] at hfinal
  refine ⟨j, k, B, hB, hBind, ?_⟩
  simpa only [expect_prod_split, sample, one_mul] using
    (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfinal t ht)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
