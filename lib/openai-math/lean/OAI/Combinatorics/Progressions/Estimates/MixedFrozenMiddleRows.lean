/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.MixedRootLosses
import OAI.Combinatorics.Progressions.Geometry.BinaryWordSupports

namespace OAI

section

namespace Erdos3

open scoped BigOperators

abbrev MixedWeightCorner (s k : ℕ) :=
  {v : Fin (s + 3) → Fin 2 // mixedCornerWeight v = k}

def mixedWeightSupportEquiv (s k : ℕ) :
    MixedWeightCorner s k ≃ {S : Finset (Fin (s + 3)) // S.card = k} :=
  (binaryWordSupportEquiv (s + 3)).subtypeEquiv (fun v => by
    change mixedCornerWeight v = k ↔ (binaryWordSupport v).card = k
    rw [binaryWordSupport_card]
    rfl)

theorem mixedWeightCorner_card (s k : ℕ) :
    Fintype.card (MixedWeightCorner s k) = (s + 3).choose k := by
  calc
    _ = Fintype.card {S : Finset (Fin (s + 3)) // S.card = k} :=
      Fintype.card_congr (mixedWeightSupportEquiv s k)
    _ = _ := by simpa only [Fintype.card_fin] using
      Fintype.card_finset_len (α := Fin (s + 3)) k

theorem mixedCornerWeight_zero_iff {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v = 0 ↔ v = fun _ => 0 := by
  constructor
  · intro h
    have hc : (binaryWordSupport v).card = 0 := by
      simpa only [binaryWordSupport_card, mixedCornerWeight] using h
    apply (binaryWordSupportEquiv (s + 3)).injective
    exact (Finset.card_eq_zero.mp hc).trans (binaryWordSupport_zero (s + 3)).symm
  · rintro rfl
    simp [mixedCornerWeight]

theorem mixedCornerWeight_le {s : ℕ} (v : Fin (s + 3) → Fin 2) :
    mixedCornerWeight v ≤ s + 3 := by
  have h := (binaryWordSupport v).card_le_univ
  simpa only [binaryWordSupport_card, Fintype.card_fin, mixedCornerWeight] using h

theorem mixedCornerWeight_pos {s : ℕ} (v : MixedNonconstantCorner s) :
    0 < mixedCornerWeight v.val := by
  have h : mixedCornerWeight v.val ≠ 0 := fun h => v.property ((mixedCornerWeight_zero_iff _).mp h)
  omega

noncomputable def mixedWeightOneEquiv (s : ℕ) : Fin (s + 3) ≃ MixedWeightCorner s 1 :=
  (Fintype.equivFinOfCardEq (by simp only [mixedWeightCorner_card, Nat.choose_one_right])).symm

def mixedWeightSample (s : ℕ) (k : Fin (s + 3)) : Fin (s + 3) → Fin 2 :=
  fun j => if j.val < k.val + 1 then 0 else 1

end Erdos3

end

section

namespace Erdos3

abbrev MixedWeightBlock (s : ℕ) := (k : Fin (s + 3)) × MixedWeightCorner s (k.val + 1)

def mixedWeightBlockCorner {s : ℕ} (z : MixedWeightBlock s) : MixedNonconstantCorner s :=
  ⟨z.2.val, by
    intro h
    have hz := (mixedCornerWeight_zero_iff z.2.val).mpr h
    rw [z.2.property] at hz
    omega⟩

theorem mixedWeightBlockCorner_injective (s : ℕ) :
    Function.Injective (mixedWeightBlockCorner (s := s)) := by
  rintro ⟨i, v⟩ ⟨j, w⟩ h
  have hvw : v.val = w.val := congrArg Subtype.val h
  have hij : i.val + 1 = j.val + 1 :=
    v.property.symm.trans ((congrArg mixedCornerWeight hvw).trans w.property)
  have hi : i = j := Fin.ext (by omega)
  subst j
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hvw))

theorem mixedWeightBlockCorner_surjective (s : ℕ) :
    Function.Surjective (mixedWeightBlockCorner (s := s)) := by
  intro v
  have hp := mixedCornerWeight_pos v
  have hl := mixedCornerWeight_le v.val
  let k : Fin (s + 3) := ⟨mixedCornerWeight v.val - 1, by omega⟩
  have hk : mixedCornerWeight v.val = k.val + 1 := by dsimp [k]; omega
  exact ⟨⟨k, ⟨v.val, hk⟩⟩, Subtype.ext rfl⟩

noncomputable def mixedWeightBlockEquiv (s : ℕ) : MixedWeightBlock s ≃ MixedNonconstantCorner s :=
  Equiv.ofBijective mixedWeightBlockCorner
    ⟨mixedWeightBlockCorner_injective s, mixedWeightBlockCorner_surjective s⟩

theorem mixedWeightBlock_canonical {s : ℕ} (z : MixedWeightBlock s) :
    mixedCanonicalSample (mixedWeightBlockEquiv s z).val = mixedWeightSample s z.1 := by
  change (fun j : Fin (s + 3) => if j.val < mixedCornerWeight z.2.val then (0 : Fin 2) else 1) =
    (fun j : Fin (s + 3) => if j.val < z.1.val + 1 then 0 else 1)
  rw [z.2.property]

noncomputable def mixedWeightMerge {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I)
    (v : MixedNonconstantCorner s) : I :=
  a ((mixedWeightBlockEquiv s).symm v).1 ((mixedWeightBlockEquiv s).symm v).2

theorem mixedWeightMerge_block {s : ℕ} {I : Type*}
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → I) (z : MixedWeightBlock s) :
    mixedWeightMerge a (mixedWeightBlockEquiv s z) = a z.1 z.2 := by
  unfold mixedWeightMerge
  rw [Equiv.symm_apply_apply]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedWeightSample_first_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s 0) x =
      fun j : MixedReplicatedIndex (s + 2) => x j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · change x (if i.succ.val < (0 : Fin (s + 3)).val + 1 then 0 else 1) = x 1
    rw [ite_eq_right (by simp only [Fin.val_succ, Fin.val_zero]; omega)]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedWeightTensor (k : Fin (s + 3))
    (a : MixedWeightCorner s (k.val + 1) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedSampledInput (mixedWeightSample s k) x)

noncomputable def mixedFirstTensor (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval (s + 3) a (fun j => x j.1)

theorem mixedWeightTensor_norm (k : Fin (s + 3))
    (a : MixedWeightCorner s (k.val + 1) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedWeightTensor k a x‖ ≤ 1 := by
  rw [mixedWeightTensor, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedWeightTensor_unit (k : Fin (s + 3)) (x : Fin 2 → ℤ) :
    ∑ a : MixedWeightCorner s (k.val + 1) → Fin W.outputDim, ‖W.mixedWeightTensor k a x‖ ^ 2 = 1 := by
  simp only [mixedWeightTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ _v : MixedWeightCorner s (k.val + 1), ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedSampledInput (mixedWeightSample s k) x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem mixedFirstTensor_norm (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedFirstTensor a x‖ ≤ 1 := by
  rw [mixedFirstTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedFirstTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin (s + 3) → Fin W.outputDim, ‖W.mixedFirstTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval (s + 3) _

theorem mixedWeightTensor_first (a : Fin (s + 3) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x = W.mixedFirstTensor a x := by
  unfold mixedWeightTensor mixedFirstTensor tensorVector
  rw [mixedWeightSample_first_input]
  exact (mixedWeightOneEquiv s).symm.prod_comp
    (fun d : Fin (s + 3) => W.eval (a d) (fun j => x j.1))

theorem mixedCanonicalTensor_weight_merge
    (a : (k : Fin (s + 3)) → MixedWeightCorner s (k.val + 1) → Fin W.outputDim)
    (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedWeightMerge a) x) = ∏ k, W.mixedWeightTensor k (a k) x := by
  rw [mixedCanonicalTensor, star_star]
  calc
    _ = ∏ z : MixedWeightBlock s,
        W.eval (mixedWeightMerge a (mixedWeightBlockEquiv s z))
          (mixedSampledInput (mixedCanonicalSample (mixedWeightBlockEquiv s z).val) x) :=
      ((mixedWeightBlockEquiv s).prod_comp _).symm
    _ = ∏ z : MixedWeightBlock s,
        W.eval (a z.1 z.2) (mixedSampledInput (mixedWeightSample s z.1) x) := by
      apply Finset.prod_congr rfl
      intro z _
      rw [mixedWeightMerge_block, mixedWeightBlock_canonical]
    _ = _ := by simp only [Fintype.prod_sigma, mixedWeightTensor]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedHigherCorner (s : ℕ) := (k : Fin (s + 2)) × MixedWeightCorner s (k.val + 2)

noncomputable def mixedGroupedWeightMerge {s : ℕ} {I : Type*}
    (a : Fin (s + 3) → I) (b : MixedHigherCorner s → I) : MixedNonconstantCorner s → I :=
  mixedWeightMerge (Fin.cases (motive := fun k : Fin (s + 3) => MixedWeightCorner s (k.val + 1) → I)
    (fun v => a ((mixedWeightOneEquiv s).symm v)) (fun k v => b ⟨k, v⟩))

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedHigherTensor (b : MixedHigherCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x)

theorem mixedHigherTensor_norm (b : MixedHigherCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedHigherTensor b x‖ ≤ 1 := by
  rw [mixedHigherTensor, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedHigherTensor_unit (x : Fin 2 → ℤ) :
    ∑ b : MixedHigherCorner s → Fin W.outputDim, ‖W.mixedHigherTensor b x‖ ^ 2 = 1 := by
  simp only [mixedHigherTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ z : MixedHigherCorner s, ∑ i : Fin W.outputDim,
        ‖W.eval i (mixedSampledInput (mixedWeightSample s z.1.succ) x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem mixedCanonicalTensor_grouped_merge (a : Fin (s + 3) → Fin W.outputDim)
    (b : MixedHigherCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedGroupedWeightMerge a b) x) =
      W.mixedFirstTensor a x * W.mixedHigherTensor b x := by
  rw [mixedGroupedWeightMerge, W.mixedCanonicalTensor_weight_merge, Fin.prod_univ_succ]
  change W.mixedWeightTensor 0 (fun v => a ((mixedWeightOneEquiv s).symm v)) x *
    (∏ k : Fin (s + 2), W.mixedWeightTensor k.succ (fun v => b ⟨k, v⟩) x) = _
  rw [W.mixedWeightTensor_first]
  congr 1
  exact (Fintype.prod_sigma (fun z : MixedHigherCorner s =>
    W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.succ) x))).symm

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_original_mixed_first_tensor_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C) M.eval W.mixedIntegrationRoot.mixedFirstTensor := by
  obtain ⟨C, hC, h⟩ := exists_original_mixed_root_equivalence s
  refine ⟨C, hC, ?_⟩
  intro p M W E
  exact h M W E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedMiddleCorner (s : ℕ) := (k : Fin (s + 1)) × MixedWeightCorner s (k.val + 2)

def mixedSplitHigherMerge {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (z : MixedHigherCorner s) : I :=
  if h : z.1.val < s + 1 then b ⟨⟨z.1.val, h⟩, z.2⟩ else c

theorem mixedSplitHigherMerge_castSucc {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (k : Fin (s + 1)) (v : MixedWeightCorner s (k.val + 2)) :
    mixedSplitHigherMerge b c ⟨k.castSucc, v⟩ = b ⟨k, v⟩ := by
  simp only [mixedSplitHigherMerge, Fin.val_castSucc, dite_eq_left k.isLt]

theorem mixedSplitHigherMerge_last {s : ℕ} {I : Type*} (b : MixedMiddleCorner s → I) (c : I)
    (v : MixedWeightCorner s (s + 3)) :
    mixedSplitHigherMerge b c ⟨Fin.last (s + 1), v⟩ = c := by
  unfold mixedSplitHigherMerge
  exact dite_eq_right (Nat.lt_irrefl (s + 1))

theorem mixedWeightSample_last_input (s : ℕ) (x : Fin 2 → ℤ) :
    mixedSampledInput (mixedWeightSample s (Fin.last (s + 1)).succ) x = fun _ => x 0 := by
  have hs : mixedWeightSample s (Fin.last (s + 1)).succ = fun _ => (0 : Fin 2) := by
    funext j
    unfold mixedWeightSample
    apply ite_eq_left
    simpa only [Fin.val_succ, Fin.val_last] using j.isLt
  rw [hs, ← mixedSampledInput_coordinates]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedMiddleTensor (b : MixedMiddleCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∏ z, W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)

theorem mixedMiddleTensor_norm (b : MixedMiddleCorner s → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedMiddleTensor b x‖ ≤ 1 := by
  rw [mixedMiddleTensor, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedMiddleTensor_unit (x : Fin 2 → ℤ) :
    ∑ b : MixedMiddleCorner s → Fin W.outputDim, ‖W.mixedMiddleTensor b x‖ ^ 2 = 1 := by
  simp only [mixedMiddleTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ z : MixedMiddleCorner s, ∑ i : Fin W.outputDim,
        ‖W.eval i (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem mixedHigherTensor_split (b : MixedMiddleCorner s → Fin W.outputDim)
    (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedHigherTensor (mixedSplitHigherMerge b c) x =
      W.mixedMiddleTensor b x * W.eval c (fun _ => x 0) := by
  unfold mixedHigherTensor
  rw [Fintype.prod_sigma, Fin.prod_univ_castSucc]
  congr 1
  · simp only [mixedSplitHigherMerge_castSucc]
    exact (Fintype.prod_sigma (fun z : MixedMiddleCorner s =>
      W.eval (b z) (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) x))).symm
  · simp only [Fin.val_last, mixedSplitHigherMerge_last, mixedWeightSample_last_input,
      Finset.prod_const, Finset.card_univ, mixedWeightCorner_card, Nat.choose_self, pow_one]

theorem mixedCanonicalTensor_split_merge (a : Fin (s + 3) → Fin W.outputDim)
    (b : MixedMiddleCorner s → Fin W.outputDim) (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.mixedCanonicalTensor (mixedGroupedWeightMerge a (mixedSplitHigherMerge b c)) x) =
      W.mixedFirstTensor a x * (W.mixedMiddleTensor b x * W.eval c (fun _ => x 0)) := by
  rw [W.mixedCanonicalTensor_grouped_merge, W.mixedHigherTensor_split]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ}
  (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedOriginalWeightCorrection
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
    (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
      F a (mixedGroupedWeightMerge d b) x

theorem mixedOriginalWeightCorrection_pointwise_error
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim)
    (x : Fin 2 → ℤ) (D : ℂ) :
    ‖D * (M.eval i x * W.mixedIntegrationRoot.mixedHigherTensor b x) -
      M.mixedOriginalWeightCorrection W F a i b x‖ ≤
      ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
        ‖D * star (W.mixedIntegrationRoot.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x) -
          F a (mixedGroupedWeightMerge d b) x‖ := by
  let R := W.mixedIntegrationRoot
  have hres := complex_unit_vector_resolution (fun d => R.mixedFirstTensor d x)
    (R.mixedFirstTensor_unit x) (M.eval i x)
  have heq : D * (M.eval i x * R.mixedHigherTensor b x) =
      ∑ d : Fin (s + 3) → Fin R.outputDim,
        (M.eval i x * star (R.mixedFirstTensor d x)) *
          (D * star (R.mixedCanonicalTensor (mixedGroupedWeightMerge d b) x)) := by
    calc
      _ = D * ((∑ d, (M.eval i x * star (R.mixedFirstTensor d x)) * R.mixedFirstTensor d x) *
          R.mixedHigherTensor b x) := by rw [← hres]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [R.mixedCanonicalTensor_grouped_merge]
        ring
  rw [heq, mixedOriginalWeightCorrection, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [← mul_sub, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (M.norm_eval i x)).trans
    (R.mixedFirstTensor_norm d x)

theorem mixedOriginalWeightCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ)
    (D : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
      (Fin 2 → ZMod N) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * star (W.mixedIntegrationRoot.mixedCanonicalTensor b (fun k => ((x k).val : ℤ))) -
        F a b (fun k => ((x k).val : ℤ))‖) ≤ ε)
    (a : Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim)
    (i : Fin M.outputDim) (b : MixedHigherCorner s → Fin W.mixedIntegrationRoot.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖D a x * (M.eval i (fun k => ((x k).val : ℤ)) *
          W.mixedIntegrationRoot.mixedHigherTensor b (fun k => ((x k).val : ℤ))) -
        M.mixedOriginalWeightCorrection W F a i b (fun k => ((x k).val : ℤ))‖) ≤
      (W.mixedIntegrationRoot.outputDim : ℝ) ^ (s + 3) * ε := by
  have hm := Finset.expect_le_expect (s := Finset.univ)
    (fun (x : Fin 2 → ZMod N) _ => M.mixedOriginalWeightCorrection_pointwise_error W F a i b
      (fun k => ((x k).val : ℤ)) (D a x))
  rw [Finset.expect_sum_comm] at hm
  apply hm.trans
  calc
    _ ≤ ∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ε :=
      Finset.sum_le_sum (fun d _ => herr a (mixedGroupedWeightMerge d b))
    _ = _ := by simp

theorem exists_mixedOriginalWeightCorrection_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (s + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p), 0 ≤ q →
      NativeIntegerVectorEquivalence (s + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      ∀ F : (Fin W.mixedIntegrationRoot.outputDim × Fin W.mixedIntegrationRoot.outputDim) →
        (MixedNonconstantCorner s → Fin W.mixedIntegrationRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) q (F a b))) →
      ∀ a i b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
        (M.mixedOriginalWeightCorrection W F a i b)) := by
  obtain ⟨A, _, hcompare⟩ := exists_original_mixed_first_tensor_equivalence s
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let n := (s + 3) ^ (s + 2)
  let K := (s + 3) * (n + 1)
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C B) ^ B + Polynomial.C K * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p q M W hq E F hF a i b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let t := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by
    have hh : 0 ≤ (v + A) ^ A := by positivity
    dsimp [t, v] at *
    linarith
  have hAt : (p + A) ^ A ≤ t := by
    apply (pow_le_pow_left₀ (by positivity) (show p + A ≤ v + A by dsimp [v]; linarith) A).trans
    dsimp [t]
    linarith
  have hterm (d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((t + B) ^ B)
        (fun x => (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) *
          F a (mixedGroupedWeightMerge d b) x)) :=
    hmul ht ((Classical.choice ((hcompare M W E).expansion i d)).mono hAt)
      ((Classical.choice (hF a (mixedGroupedWeightMerge d b))).mono hqt)
  have hcard : (Fintype.card (Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim) : ℝ) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (s + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) W.mixedIntegrationRoot.output_bound _
      _ = Real.exp (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) :=
        (Real.exp_nat_mul (tensorPowerBudget n p) (s + 3)).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have heq : (((s + 3 : ℕ) : ℝ) * tensorPowerBudget n p) = (K : ℝ) * (p + 1) := by
          simp only [K, tensorPowerBudget, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by dsimp [v]; linarith) (Nat.cast_nonneg _)
  have hcoeff : (∑ _ : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim, ‖(1 : ℂ)‖) ≤
      Real.exp ((K : ℝ) * (v + 1)) := by simpa using hcard
  have H := NativeIntegerExpansion.weightedSum (fun d => Classical.choice (hterm d))
    (fun _ => (1 : ℂ)) (by positivity : 0 ≤ (K : ℝ) * (v + 1)) hcard hcoeff
  have hcost : (t + B) ^ B + (K : ℝ) * (v + 1) ≤ (p + q + C) ^ C := by
    simpa [X, T, t, v, Polynomial.eval₂_pow] using hbudget v hv
  refine ⟨?_⟩
  change NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + q + C) ^ C)
    (fun x => ∑ d : Fin (s + 3) → Fin W.mixedIntegrationRoot.outputDim,
      (M.eval i x * star (W.mixedIntegrationRoot.mixedFirstTensor d x)) * F a (mixedGroupedWeightMerge d b) x)
  simpa only [one_mul] using H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_middle_factor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (k : Fin (s + 1)) (a : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (fun _ : MixedReplicatedIndex (s + 2) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W h k a
  classical
  let S : Finset (MixedReplicatedIndex (s + 2)) :=
    Finset.univ.image (fun i : Fin (s + 1) => mixedReplica i.succ)
  let A : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then 0 else 1
  let b : MixedReplicatedIndex (s + 2) → ℤ :=
    fun j => if (mixedInputCoordinate (s + 1) j).val < k.val + 2 then h else 0
  have hA : ∀ j, j ∉ S → A j = 0 := by
    intro j hj
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · change (if (0 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
      simp
    · revert hj
      refine Fin.cases ?_ (fun i => ?_) i
      · intro _
        change (if (1 : ℕ) < k.val + 2 then (0 : ℤ) else 1) = 0
        split_ifs <;> omega
      · intro hj
        exact False.elim (hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hi : Function.Injective (fun i : Fin (s + 1) => mixedReplica i.succ) := by
    intro i j hij
    exact Fin.succ_injective _ (mixedReplica_injective _ hij)
  have hc : S.card = s + 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hi]
    simp
  have hdegree : (∑ i ∈ S, (fun _ : MixedReplicatedIndex (s + 2) => 1) i) = s + 1 := by
    simpa using hc
  obtain ⟨E, _⟩ := hfreeze W S A b a hA
  have hin (x : Unit → ℤ) : (fun j => b j + A j * x ()) =
      mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()] := by
    rw [← mixedSampledInput_coordinates]
    funext j
    simp only [A, b, mixedWeightSample, Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]
    split_ifs <;> simp
  have heq : (fun x : Unit → ℤ => W.eval a (fun j => b j + A j * x ())) =
      (fun x => W.eval a (mixedSampledInput (mixedWeightSample s k.castSucc.succ) ![h, x ()])) := by
    funext x
    rw [hin]
  rw [hdegree, heq] at E
  exact ⟨E⟩

theorem exists_mixedMiddleTensor_row_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)
      (h : ℤ) (b : MixedMiddleCorner s → Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C)
        (fun x => W.mixedMiddleTensor b ![h, x ()])) := by
  obtain ⟨A, _, hfactor⟩ := exists_mixed_middle_factor_row_expansion s
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (Fintype.card (MixedMiddleCorner s))
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W h b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let e := (Fintype.equivFin (MixedMiddleCorner s)).symm
  obtain ⟨F⟩ := hprod
    (fun i (x : Unit → ℤ) => W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()]))
    (by positivity : 0 ≤ (p + A) ^ A) (fun i => hfactor W h (e i).1 (b (e i)))
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => ∏ i, W.eval (b (e i))
      (mixedSampledInput (mixedWeightSample s (e i).1.castSucc.succ) ![h, x ()])) =
      (fun x => W.mixedMiddleTensor b ![h, x ()]) := by
    funext x
    exact e.prod_comp (fun z => W.eval (b z)
      (mixedSampledInput (mixedWeightSample s z.1.castSucc.succ) ![h, x ()]))
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
