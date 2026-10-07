/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.QuarticRootExchange
import OAI.Combinatorics.Progressions.Linear.MixedSumKernelCorrelation

namespace OAI

section

namespace Erdos3

def mixedSampledInput {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (d + 2) → ℤ :=
  mixedReplicatedInput (x (π 0)) (fun j => x (π j.succ))

theorem mixedSampledInput_slots {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    mixedSampledInput π x =
      mixedSlotInput (x (π 0)) (x (π 1)) (fun j => x (π j.succ.succ)) := by
  unfold mixedSampledInput mixedSlotInput
  congr 1
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem mixedSampledInput_coordinates {d : ℕ} (π : Fin (d + 3) → Fin 2) (x : Fin 2 → ℤ) :
    (fun j => x (π (mixedInputCoordinate (d + 1) j))) = mixedSampledInput π x := by
  exact (mixedInputCoordinate_eval (d + 1) (fun k => x (π k))).trans
    (mixedSampledInput_slots π x).symm

theorem mixedSampledInput_map {d : ℕ} (π : Fin (d + 3) → Fin 2)
    (g : ℤ → ℤ) (x : Fin 2 → ℤ) :
    mixedSampledInput π (fun k => g (x k)) = fun k => g (mixedSampledInput π x k) := by
  rw [← mixedSampledInput_coordinates, ← mixedSampledInput_coordinates]

def mixedPermuteSample {d : ℕ} (e : Equiv.Perm (Fin (d + 2)))
    (π : Fin (d + 3) → Fin 2) : Fin (d + 3) → Fin 2 :=
  Fin.cases (π 0) (fun j => π (e j).succ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedCoordinateIndex_coordinate (n : ℕ) (j : MixedReplicatedIndex (n + 1)) :
    mixedCoordinateIndex n (mixedInputCoordinate n j) = j := by
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

def mixedAllCoordinates (s : ℕ) : List (MixedReplicatedIndex (s + 2)) :=
  List.ofFn (mixedCoordinateIndex (s + 1))

theorem mixedAllCoordinates_length (s : ℕ) : (mixedAllCoordinates s).length = s + 3 := by
  simp only [mixedAllCoordinates, List.length_ofFn]

theorem mixedAllCoordinates_nodup (s : ℕ) : (mixedAllCoordinates s).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Function.LeftInverse.injective (mixedInputCoordinate_index (s + 1))

theorem mixedAllCoordinates_get (s : ℕ) (j : Fin (mixedAllCoordinates s).length) :
    (mixedAllCoordinates s).get j =
      mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) j) := by
  exact List.get_ofFn (mixedCoordinateIndex (s + 1)) j

theorem mem_mixedAllCoordinates (s : ℕ) (j : MixedReplicatedIndex (s + 2)) :
    j ∈ mixedAllCoordinates s := by
  apply List.mem_ofFn.mpr
  exact ⟨mixedInputCoordinate (s + 1) j, mixedCoordinateIndex_coordinate (s + 1) j⟩

def mixedCornerAssignmentEquiv (s : ℕ) :
    (Fin (mixedAllCoordinates s).length → Fin 2) ≃ (Fin (s + 3) → Fin 2) where
  toFun v j := v (Fin.cast (mixedAllCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedAllCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedDiagonalCorner {s : ℕ} (v : Fin (s + 3) → Fin 2) (x : Fin 2 → ℤ) :
    MixedReplicatedIndex (s + 2) → ℤ := mixedSampledInput (fun k => (v k).rev) x

theorem mixedDiagonalCorner_zero {s : ℕ} (x : Fin 2 → ℤ) :
    mixedDiagonalCorner (fun _ : Fin (s + 3) => 0) x = fun _ => x 1 := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  rfl

def mixedDiagonalChoiceInput {s : ℕ} (x : Fin 2 → ℤ)
    (j : Fin 2 × MixedReplicatedIndex (s + 2)) : ℤ := x j.1.rev

theorem mixedDiagonalChoice_sum (s : ℕ) (x : Fin 2 → ℤ) :
    finiteChoiceCoordinateInput (mixedAllCoordinates s) (mixedDiagonalChoiceInput x) =
      fun _ => x 1 + x 0 := by
  funext j
  simp only [finiteChoiceCoordinateInput, mem_mixedAllCoordinates, ite_true,
    mixedDiagonalChoiceInput]
  change (∑ a : Fin 2, x a.rev) = x 1 + x 0
  exact Fin.sum_univ_two (fun a : Fin 2 => x a.rev)

theorem mixedDiagonalChoice_leaf (s : ℕ) (x : Fin 2 → ℤ)
    (v : Fin (mixedAllCoordinates s).length → Fin 2) :
    finiteChoiceLeafInput (mixedAllCoordinates s) v (mixedDiagonalChoiceInput x) =
      mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x := by
  rw [mixedDiagonalCorner, ← mixedSampledInput_coordinates]
  funext j
  let k : Fin (mixedAllCoordinates s).length :=
    Fin.cast (mixedAllCoordinates_length s).symm (mixedInputCoordinate (s + 1) j)
  have H := finiteChoiceLeafInput_get (mixedAllCoordinates s)
    (mixedAllCoordinates_nodup s) v (mixedDiagonalChoiceInput x) k
  rw [mixedAllCoordinates_get] at H
  have hk : mixedCoordinateIndex (s + 1) (Fin.cast (mixedAllCoordinates_length s) k) = j :=
    mixedCoordinateIndex_coordinate (s + 1) j
  rw [hk] at H
  exact H

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalTensor
    (a : (Fin (s + 3) → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (mixedDiagonalCorner v x)

theorem mixedDiagonalTensor_norm
    (a : (Fin (s + 3) → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.mixedDiagonalTensor a x‖ ≤ 1 := by
  rw [mixedDiagonalTensor, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedDiagonalTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : (Fin (s + 3) → Fin 2) → Fin W.outputDim, ‖W.mixedDiagonalTensor a x‖ ^ 2 = 1 := by
  simp only [mixedDiagonalTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : Fin (s + 3) → Fin 2, ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedDiagonalCorner v x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_diagonal_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
        W.mixedDiagonalTensor := by
  let : Nonempty (MixedReplicatedIndex (s + 2)) := replicatedMixed_nonempty (s + 2)
  obtain ⟨C, hC, hexpand⟩ := exists_finite_assignment_equivalence 1 (mixedAllCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p W
  let a : Fin 2 × MixedReplicatedIndex (s + 2) → Fin 2 := fun j => j.1.rev
  have hA (x : Fin 2 → ℤ) : (fun j => x (a j)) = mixedDiagonalChoiceInput x := rfl
  have E := (hexpand W (mixedAllCoordinates_nodup s)).coordinatePullback a
  have H : NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (fun _ => x 1 + x 0))
      (fun b : (Fin (mixedAllCoordinates s).length → Fin 2) → Fin W.outputDim =>
        fun x => ∏ v, W.eval (b v) (mixedDiagonalCorner (mixedCornerAssignmentEquiv s v) x)) := by
    simpa only [hA, finiteChoiceExpansion, mixedDiagonalChoice_sum, mixedDiagonalChoice_leaf,
      replicatedMixed_card, Nat.add_sub_cancel] using E
  have hdim : (Fintype.card ((Fin (s + 3) → Fin 2) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, mixedAllCoordinates_length]
      using H.right_dimension
  apply H.of_coordinate_maps _ W.mixedDiagonalTensor id
    (fun b v => b (mixedCornerAssignmentEquiv s v)) (fun _ _ => rfl) _
    H.left_dimension hdim le_rfl
  intro b x
  exact ((mixedCornerAssignmentEquiv s).prod_comp
    (fun v => W.eval (b v) (mixedDiagonalCorner v x))).symm

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev MixedNonconstantCorner (s : ℕ) := {v : Fin (s + 3) → Fin 2 // v ≠ fun _ => 0}

theorem mixedNonconstantCorner_card (s : ℕ) :
    Fintype.card (MixedNonconstantCorner s) = 2 ^ (s + 3) - 1 := by
  simp [MixedNonconstantCorner, Fintype.card_subtype_compl]

namespace NativeMultidegreeNilcharacter

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedDiagonalDerivative (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0))

noncomputable def mixedNonconstantTensor (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star (∏ v, W.eval (a v) (mixedDiagonalCorner v.val x))

theorem mixedDiagonalDerivative_norm (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedNonconstantTensor_norm (a : MixedNonconstantCorner s → Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedNonconstantTensor a x‖ ≤ 1 := by
  rw [mixedNonconstantTensor, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem mixedDiagonalDerivative_unit (x : Fin 2 → ℤ) :
    ∑ a, ‖W.mixedDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [mixedDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem mixedNonconstantTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : MixedNonconstantCorner s → Fin W.outputDim, ‖W.mixedNonconstantTensor a x‖ ^ 2 = 1 := by
  simp only [mixedNonconstantTensor, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : MixedNonconstantCorner s, ∑ a : Fin W.outputDim,
        ‖W.eval a (mixedDiagonalCorner v.val x)‖ ^ 2 := (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem exists_mixed_diagonal_derivative_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p),
      NativeIntegerVectorEquivalence (s + 2) ((p + C) ^ C)
        W.mixedDiagonalDerivative W.mixedNonconstantTensor := by
  obtain ⟨A, _, hdiag⟩ := exists_mixed_diagonal_expansion s
  let m : ℕ := 2 ^ (s + 3) - 1
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C m * X + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hsum : (p + A) ^ A + (m : ℝ) * p + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hm : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hnonconstant : (m : ℝ) * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hdimNonconstant : (Fintype.card (MixedNonconstantCorner s → Fin W.outputDim) : ℝ) ≤
      Real.exp ((m : ℝ) * p) := by
    simp only [Fintype.card_fun, mixedNonconstantCorner_card, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound m
      _ = _ := (Real.exp_nat_mul p m).symm
  refine ⟨(card_product_le_exp_two hdim hdim).trans (Real.exp_le_exp.mpr htwo),
    hdimNonconstant.trans (Real.exp_le_exp.mpr hnonconstant), ?_⟩
  intro a b
  let full : (Fin (s + 3) → Fin 2) → Fin W.outputDim := fun v =>
    if h : v = fun _ => 0 then a.1 else b ⟨v, h⟩
  obtain ⟨F⟩ := (hdiag W).expansion a.2 full
  have htensor (x : Fin 2 → ℤ) : W.mixedDiagonalTensor full x =
      W.eval a.1 (fun _ => x 1) *
        ∏ v : MixedNonconstantCorner s, W.eval (b v) (mixedDiagonalCorner v.val x) := by
    rw [mixedDiagonalTensor, Fintype.prod_eq_mul_prod_subtype_ne _ (fun _ => 0)]
    have hzero : full (fun _ => 0) = a.1 := by simp only [full, dite_eq_left rfl]
    have hfull (v : MixedNonconstantCorner s) : full v.val = b v := by
      simp only [full, dite_eq_right v.property]
    simp only [hzero, mixedDiagonalCorner_zero, hfull]
  have heq : (fun x : Fin 2 → ℤ => star (W.eval a.2 (fun _ => x 1 + x 0) *
      star (W.mixedDiagonalTensor full x))) =
      (fun x => W.mixedDiagonalDerivative a x * star (W.mixedNonconstantTensor b x)) := by
    funext x
    rw [htensor]
    simp only [mixedDiagonalDerivative, mixedNonconstantTensor, star_mul, star_star]
    ring
  exact ⟨heq ▸ F.conjugate.mono hcost⟩

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedReplicated_totalDegree (n : ℕ) :
    (∑ _ : MixedReplicatedIndex (n + 1), (1 : ℕ)) = n + 2 := by
  have hc : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 := replicatedMixed_card (n + 1)
  rw [Finset.sum_const, Finset.card_univ, hc]
  simp

namespace NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {n : ℕ} {p : ℝ}
  (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)

noncomputable def mixedPairComponent (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    W.model.Niltest (fun _ : Fin (n + 2) => 1) :=
  (W.component out).linearPullbackHom (fun j =>
    { toFun := fun x => x (v (mixedInputCoordinate n j))
      map_zero' := rfl
      map_add' := fun _ _ => rfl })

theorem mixedPairComponent_eval (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (x : Fin (n + 2) → ℤ) :
    (W.mixedPairComponent out v).eval x =
      W.eval out (mixedSlotInput (x (v 0)) (x (v 1)) (fun j => x (v j.succ.succ))) := by
  rw [mixedPairComponent, Niltest.eval_linearPullbackHom, component_eval]
  exact congrArg (W.eval out) (mixedInputCoordinate_eval n (fun j => x (v j)))

theorem mixedPairComponent_complexity (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    (W.mixedPairComponent out v).ComplexityLE (p + 4) := W.component_complexity out

theorem mixedPairComponent_vertical (out : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2))
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : W.model.Space) :
    (W.mixedPairComponent out v).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.mixedPairComponent out v).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

theorem mixedPairComponent_orbit_eq (out out' : Fin W.outputDim) (v : Fin (n + 2) → Fin (n + 2)) :
    (W.mixedPairComponent out v).orbit = (W.mixedPairComponent out' v).orbit := rfl

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def mixedIntegrationRoot {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) :
    NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1)
      (tensorPowerBudget ((d + 3) ^ (d + 2)) p) :=
  (W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)).tensorPower ((d + 3) ^ (d + 2))

theorem mixedIntegrationRoot_dim {d : ℕ} {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p) :
    W.mixedIntegrationRoot.dim = W.dim := rfl

theorem exists_mixed_integration_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        W.eval (tensorVector W.mixedIntegrationRoot.eval (d + 3)) := by
  obtain ⟨a, _, hdilation⟩ := exists_uniform_dilation_degree_equivalence (d + 2) ((d + 3 : ℕ) : ℤ)
  let n := (d + 3) ^ (d + 2)
  let X : Polynomial ℕ := Polynomial.X
  let B := Polynomial.C (n + 1) * (X + 1)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C (d + 4) * B + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + a) ^ a := by positivity
  have hB : 0 ≤ tensorPowerBudget n p := by unfold tensorPowerBudget; positivity
  have hqB : 0 ≤ (d + 3 : ℝ) * tensorPowerBudget n p := by positivity
  have hb : (p + a) ^ a + (d + 4 : ℝ) * tensorPowerBudget n p + p + 2 ≤ (p + C) ^ C := by
    simpa [X, B, tensorPowerBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by nlinarith
  have hAr : (p + a) ^ a ≤ (p + C) ^ C := by nlinarith
  have hdimBound : (d + 3 : ℝ) * tensorPowerBudget n p ≤ (p + C) ^ C := by nlinarith
  let V := W.rationalDilation (((d + 3 : ℕ) : ℚ)⁻¹)
  let R := V.tensorPower n
  have hscale : (((d + 3 : ℕ) : ℚ)⁻¹) * (((d + 3 : ℕ) : ℤ) : ℚ) = 1 := by
    rw [Int.cast_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
  have hleft (i : Fin W.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      W.eval i x = integerDilationVector V.eval ((d + 3 : ℕ) : ℤ) i x :=
    (W.rationalDilation_eval_rescaled _ _ hscale i x).symm
  have hpos : 1 ≤ d + 3 := by omega
  have hright (b : Fin (d + 3) → Fin R.outputDim) (x : MixedReplicatedIndex (d + 2) → ℤ) :
      tensorVector R.eval (d + 3) b x = signedTensorVector V.eval (((d + 3 : ℕ) : ℤ) ^ (d + 3))
        (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos b) x := by
    exact V.tensorPower_tensor_eval (d + 3) (d + 3) hpos b x
  have hdim : (Fintype.card (Fin (d + 3) → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget n p) ^ (d + 3) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp ((d + 3 : ℝ) * tensorPowerBudget n p) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget n p) (d + 3)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have hs : (∑ _ : MixedReplicatedIndex (d + 2), (1 : ℕ)) = d + 3 :=
    mixedReplicated_totalDegree (d + 1)
  exact (hdilation _ hs V).of_coordinate_maps W.eval (tensorVector R.eval (d + 3)) id
    (rootTensorIndex W.outputDim (d + 3) (d + 3) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {s : ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p)

noncomputable def mixedCyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

theorem mixedCyclicDiagonalDerivative_norm {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.mixedCyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [mixedCyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedCyclicDiagonalDerivative_unit {N : ℕ} [NeZero N]
    (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.mixedCyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [mixedCyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

noncomputable def mixedWrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def mixedDiagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem mixedWrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedWrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [mixedWrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedDiagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.mixedDiagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [mixedDiagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem mixedWrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.mixedWrappedDiagonalDerivative N a x =
      ∑ k, W.mixedDiagonalWrapCoefficient N a.2 k x * W.mixedDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [mixedDiagonalWrapCoefficient, mixedDiagonalDerivative]
      ring

theorem mixedCyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.mixedCyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.mixedDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.mixedWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      mixedCyclicDiagonalDerivative, mixedWrappedDiagonalDerivative]
    rw [hval, ite_eq_left hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      mixedCyclicDiagonalDerivative, mixedDiagonalDerivative]
    rw [hval, ite_eq_right hcut, sub_zero]

theorem exists_mixedDiagonalWrapCoefficient_expansion (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (s + 2) => 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C)
        (W.mixedDiagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ := exists_multidegree_integer_translation (s + 2)
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  let A : MixedReplicatedIndex (s + 2) → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := (htranslate (fun _ : MixedReplicatedIndex (s + 2) => 1) (mixedReplicated_totalDegree (s + 1)) W 0 (fun _ => -(N : ℤ))).expansion k j
  have H := F.linearPullbackHom A
  have heq : (fun x : Fin 2 → ℤ => W.eval k ((fun l => A l x) + 0) *
      star (W.eval j ((fun l => A l x) + fun _ => -(N : ℤ)))) =
      W.mixedDiagonalWrapCoefficient N j k := by
    funext x
    simp only [add_zero, mixedDiagonalWrapCoefficient, sub_eq_add_neg]
    rfl
  exact ⟨heq ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_rational_division_equivalence (d D : ℕ) [NeZero D] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p)
      (π : Fin (d + 3) → Fin 2),
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) =>
          (W.rationalDilation ((D : ℚ)⁻¹)).eval j (mixedSampledInput π x))
        (fun j x => W.eval j (mixedSampledInput π (fun k => x k / (D : ℤ)))) := by
  obtain ⟨C, hC, h⟩ := exists_sampled_rational_division_equivalence D (d + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro p W π
  simpa only [← mixedSampledInput_coordinates] using
    h (fun _ : MixedReplicatedIndex (d + 2) => 1) (mixedReplicated_totalDegree (d + 1)) W
      (fun j => π (mixedInputCoordinate (d + 1) j))

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def mixedPairBudget (p q : ℝ) : ℝ := 4 * (p + q + 1) + raisedNiltestBudget (p + q) + 6

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

abbrev MixedPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def mixedPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : MixedReplicatedIndex (n + 1), 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)) (fun _ : Fin 2 => W.model)

noncomputable def mixedPairTests :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate
  | some k => ![W.mixedPairComponent i id,
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate] k

noncomputable def mixedPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem mixedPairTests_eval (x : Fin (n + 2) → ℤ) :
    (∏ k, (V.mixedPairTests k).eval x) =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate.eval x *
    ((W.mixedPairComponent i id).eval x *
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate.eval x) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.mixedPairComponent_eval, W.mixedPairComponent_eval]
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (k : Fin n) : mixedExchangeCoordinate n k.succ.succ = k.succ.succ := rfl
  simp only [id_eq, h0, h1, ht, NativeMultidegreeNilcharacter.mixedAntisymmetric]
  ring

theorem mixedPairTests_vertical (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (V.mixedPairModels k).Space) :
    (V.mixedPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedPairFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (V.mixedPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by rw [mixedReplicated_totalDegree]; omega : n + 1 < ∑ _ : MixedReplicatedIndex (n + 1), 1) z hz x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical i id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical j (mixedExchangeCoordinate n)) z hz x

include V in
theorem mixedPairBudget_six_le : 6 ≤ mixedPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold mixedPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem mixedPairTests_complexity (k : Option (Fin 2)) :
    (V.mixedPairTests k).ComplexityLE (mixedPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold mixedPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ mixedPairBudget p q := by
      unfold mixedPairBudget
      linarith
    fin_cases k
    · exact (W.mixedPairComponent_complexity i id).mono hcost
    · exact (W.mixedPairComponent_complexity j (mixedExchangeCoordinate n)).mono hcost

end NativeSampleCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_original_mixed_root_equivalence (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree (d + 2)) p)
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (d + 2) => 1) p),
      NativeIntegerVectorEquivalence (d + 2) p M.eval
        (fun k x => W.eval k (fun j => x j.1)) →
      NativeIntegerVectorEquivalence (d + 2) ((p + C) ^ C) M.eval
        (fun a (x : Fin 2 → ℤ) => tensorVector W.mixedIntegrationRoot.eval (d + 3) a (fun j => x j.1)) := by
  obtain ⟨a, _, hroot⟩ := exists_mixed_integration_root_equivalence d
  obtain ⟨b, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p M W E
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let t := (p + a) ^ a + p
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_left (by positivity)
  have hAt : (p + a) ^ a ≤ t := le_add_of_nonneg_right hp
  have F := (hroot W).coordinatePullback (fun j : MixedReplicatedIndex (d + 2) => j.1)
  have H := htrans ht (E.mono hpt) (F.mono hAt) (fun x => W.unit_eval _)
  have hcost : (t + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, t, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
