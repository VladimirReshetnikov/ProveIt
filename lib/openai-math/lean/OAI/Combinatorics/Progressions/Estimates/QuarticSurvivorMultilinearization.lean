/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Data.Fintype.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer
import OAI.Combinatorics.Progressions.Estimates.MixedPermutationTensor
import OAI.Combinatorics.Progressions.Estimates.SecondDifferenceVectorEquivalence

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_ternary_expansion_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun j x => W.eval j (ternaryCoordinateInput l x))
        (ternaryCoordinateExpansion W.eval l) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
    refine ⟨C, hC, ?_⟩
    intro p W _
    have E := (hself W).coordinatePullback (fun j => ((0 : Fin 3), j))
    change NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
      (fun j (x : (Fin 3 × σ) → ℤ) => W.eval j (fun i => x (0, i)))
      (fun j x => W.eval j (fun i => x (0, i)))
    exact E
  | cons i l ih =>
    obtain ⟨A, _, hprevious⟩ := ih
    obtain ⟨B, _, hstep⟩ := exists_ternary_coordinate_equivalence (σ := σ)
    obtain ⟨D, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
    obtain ⟨F, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
    let X : Polynomial ℕ := Polynomial.X
    let U := (X + Polynomial.C A) ^ A
    let V := (U + Polynomial.C D) ^ D
    let T := (U + V + Polynomial.C D) ^ D
    let R := (X + Polynomial.C B) ^ B + T
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C F) ^ F)
    refine ⟨C, hC, ?_⟩
    intro p W hl
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let u := (p + A) ^ A
    let v := (u + D) ^ D
    let t := (u + v + D) ^ D
    let r := (p + B) ^ B + t
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hBt : (p + B) ^ B ≤ r := le_add_of_nonneg_right ht
    have htr : t ≤ r := le_add_of_nonneg_left (by positivity)
    have E := hprevious W hl.tail
    have E₁ := E.coordinatePullback (ternaryReplaceIndex i 1)
    have E₂ := E.coordinatePullback (ternaryReplaceIndex i 2)
    have E₁₂ := htensor hu E₁ E₂
    have Eall := htensor (add_nonneg hu hv)
      (E.mono (le_add_of_nonneg_right hv)) (E₁₂.mono (le_add_of_nonneg_left hu))
    have E' : NativeIntegerVectorEquivalence (Fintype.card σ - 1) t
        (fun a : Fin W.outputDim × (Fin W.outputDim × Fin W.outputDim) => fun x =>
          W.eval a.1 (ternaryCoordinateInput l x) *
            (W.eval a.2.1 (ternaryCoordinateInput l (ternaryReplaceInput i 1 x)) *
              W.eval a.2.2 (ternaryCoordinateInput l (ternaryReplaceInput i 2 x))))
        (ternaryCoordinateExpansion W.eval (i :: l)) := Eall
    have hunit (x : (Fin 3 × σ) → ℤ) :
        ∑ a : Fin W.outputDim × (Fin W.outputDim × Fin W.outputDim),
          ‖W.eval a.1 (ternaryCoordinateInput l x) *
            (W.eval a.2.1 (ternaryCoordinateInput l (ternaryReplaceInput i 1 x)) *
              W.eval a.2.2 (ternaryCoordinateInput l (ternaryReplaceInput i 2 x)))‖ ^ 2 = 1 := by
      simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
    have H := htrans hr ((hstep W l i (List.nodup_cons.mp hl).1).mono hBt) (E'.mono htr) hunit
    have hcost : (r + F) ^ F ≤ (p + C) ^ C := by
      simpa [X, U, V, T, R, u, v, t, r, Polynomial.eval₂_pow] using hbudget p hp
    exact H.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_ternary_assignment_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun j x => W.eval j (ternaryCoordinateInput l x))
        (fun a : (Fin l.length → Fin 3) → Fin W.outputDim => fun x =>
          ∏ v : Fin l.length → Fin 3, W.eval (a v) (ternaryLeafInput l v x)) := by
  obtain ⟨A, _, hexpand⟩ := exists_ternary_expansion_equivalence l
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C (3 ^ l.length) * X + X)
  refine ⟨C, hC, ?_⟩
  intro p W hl
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hsum : (p + A) ^ A + (3 ^ l.length : ℕ) * p + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hnp : 0 ≤ (3 ^ l.length : ℕ) * p := by positivity
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hnC : (3 ^ l.length : ℕ) * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card ((Fin l.length → Fin 3) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ (3 ^ l.length) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
      _ = Real.exp ((3 ^ l.length : ℕ) * p) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnC
  apply (hexpand W hl).of_coordinate_maps _ _ id (ternaryIndexOfFunction l.length)
    (fun _ _ => rfl) _ _ hdim hAC
  · intro a x
    exact (ternaryCoordinateExpansion_leaves W.eval l a x).symm
  · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticReplicatedIndex := ReplicatedIndex (mixedCorrelationDegree 3)

def quarticReplica (j : Fin 3) : QuarticReplicatedIndex := ⟨1, ⟨j.val, j.isLt⟩⟩

def quarticRepeatedCoordinates : List QuarticReplicatedIndex :=
  [quarticReplica 0, quarticReplica 1, quarticReplica 2]

def quarticInput (h : ℤ) (v : Fin 3 → ℤ) (j : QuarticReplicatedIndex) : ℤ :=
  if j.1 = 0 then h else if j.2.val = 0 then v 0 else if j.2.val = 1 then v 1 else v 2

def quarticTernarySample (h : ℤ) (y : Fin 3 → ℤ) (j : Fin 3 × QuarticReplicatedIndex) : ℤ :=
  if j.2.1 = 0 then h else y j.1

theorem quarticInput_diagonal (h n : ℤ) :
    quarticInput h (fun _ => n) = fun j : QuarticReplicatedIndex => correlationInput h n j.1 := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> simp [quarticInput, correlationInput] <;> rfl

theorem quarticTernarySample_sum (h : ℤ) (y : Fin 3 → ℤ) :
    ternaryCoordinateInput quarticRepeatedCoordinates (quarticTernarySample h y) =
      quarticInput h (fun _ => y 0 + y 1 + y 2) := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [ternaryCoordinateInput, quarticRepeatedCoordinates, quarticReplica,
      quarticTernarySample, quarticInput, Fin.sum_univ_three]

theorem quarticTernarySample_leaf (h : ℤ) (y : Fin 3 → ℤ) (v : Fin 3 → Fin 3) :
    ternaryLeafInput quarticRepeatedCoordinates v (quarticTernarySample h y) =
      quarticInput h (fun j => y (v j)) := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [ternaryLeafInput, quarticRepeatedCoordinates, quarticReplica,
      quarticTernarySample, quarticInput, ternaryReplaceInput, ternaryReplaceIndex,
      Fin.tail, Fin.ext_iff, -Fin.val_eq_zero_iff]

namespace NativeMultidegreeNilcharacter

theorem exists_quartic_ternary_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun j (x : Fin 4 → ℤ) => W.eval j (quarticInput (x 0) (fun _ => x 1 + x 2 + x 3)))
        (fun a : (Fin 3 → Fin 3) → Fin W.outputDim => fun x =>
          ∏ v : Fin 3 → Fin 3, W.eval (a v) (quarticInput (x 0) (fun j => x (v j).succ))) := by
  let := replicatedMixed_nonempty 3
  obtain ⟨C, hC, hexpand⟩ := exists_ternary_assignment_equivalence quarticRepeatedCoordinates
  refine ⟨C, hC, ?_⟩
  intro p W
  have hnodup : quarticRepeatedCoordinates.Nodup := by decide
  let A (j : Fin 3 × QuarticReplicatedIndex) : ((Fin 4 → ℤ) →+ ℤ) :=
    if j.2.1 = 0 then
      { toFun := fun x => x 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
    else { toFun := fun x => x j.1.succ, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hA (x : Fin 4 → ℤ) : (fun j => A j x) = quarticTernarySample (x 0) (fun j => x j.succ) := by
    funext j
    simp only [A, quarticTernarySample]
    split_ifs <;> rfl
  have E := (hexpand W hnodup).linearPullbackHom A
  change NativeIntegerVectorEquivalence (Fintype.card QuarticReplicatedIndex - 1) ((p + C) ^ C)
    (fun j (x : Fin 4 → ℤ) => W.eval j
      (ternaryCoordinateInput quarticRepeatedCoordinates (fun j => A j x)))
    (fun a : (Fin 3 → Fin 3) → Fin W.outputDim => fun x =>
      ∏ v : Fin 3 → Fin 3, W.eval (a v)
        (ternaryLeafInput quarticRepeatedCoordinates v (fun j => A j x))) at E
  have h0 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
  have h1 : (1 : Fin 3).succ = (2 : Fin 4) := rfl
  have h2 : (2 : Fin 3).succ = (3 : Fin 4) := rfl
  simpa only [hA, quarticTernarySample_sum, quarticTernarySample_leaf,
    replicatedMixed_card, Nat.reduceAdd, Nat.reduceSub, h0, h1, h2] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev QuarticBinaryAssignment := Fin 3 → Fin 2

abbrev QuarticTernaryAssignment := Fin 3 → Fin 3

abbrev QuarticSurvivor :=
  {v : QuarticTernaryAssignment // (∃ j, v j = 1) ∧ ∃ j, v j = 2}

def quarticBinaryWord (b : Fin 2) (v : QuarticBinaryAssignment) : QuarticTernaryAssignment :=
  fun j => if v j = 0 then 0 else b.succ

def quarticAssignmentMap :
    (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor → Option QuarticTernaryAssignment
  | Sum.inl (b, v) => if b = 1 ∧ v = 0 then none else some (quarticBinaryWord b v)
  | Sum.inr v => some v.val

theorem quarticAssignmentMap_bijective : Function.Bijective quarticAssignmentMap := by
  decide

noncomputable def quarticAssignmentEquiv :
    (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor ≃ Option QuarticTernaryAssignment :=
  Equiv.ofBijective quarticAssignmentMap quarticAssignmentMap_bijective

theorem quarticSurvivor_card : Fintype.card QuarticSurvivor = 12 := by
  decide

theorem quarticAssignmentMap_word
    (r : (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor) :
    (quarticAssignmentMap r).getD 0 =
      Sum.elim (fun b => quarticBinaryWord b.1 b.2) Subtype.val r := by
  rcases r with ⟨b, v⟩ | v
  · simp only [quarticAssignmentMap, Sum.elim_inl]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      funext j
      simp [quarticBinaryWord]
    · rfl
  · rfl

theorem quartic_assignment_product {I : Type*} (f : QuarticTernaryAssignment → I → ℂ)
    (a : (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor → I) :
    f 0 (a (quarticAssignmentEquiv.symm none)) *
        (∏ v : QuarticTernaryAssignment, f v (a (quarticAssignmentEquiv.symm (some v)))) =
      ((∏ v : QuarticBinaryAssignment, f (quarticBinaryWord 0 v) (a (Sum.inl (0, v)))) *
        (∏ v : QuarticBinaryAssignment, f (quarticBinaryWord 1 v) (a (Sum.inl (1, v))))) *
        ∏ v : QuarticSurvivor, f v.val (a (Sum.inr v)) := by
  let F (o : Option QuarticTernaryAssignment) := f (o.getD 0) (a (quarticAssignmentEquiv.symm o))
  calc
    _ = ∏ o : Option QuarticTernaryAssignment, F o := (Fintype.prod_option F).symm
    _ = ∏ r : (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor,
        F (quarticAssignmentEquiv r) := (quarticAssignmentEquiv.prod_comp F).symm
    _ = _ := by
      simp only [F, Equiv.symm_apply_apply]
      change (∏ r : (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor,
        f ((quarticAssignmentMap r).getD 0) (a r)) = _
      simp only [quarticAssignmentMap_word, Fintype.prod_sum_type, Fintype.prod_prod_type,
        Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticBinarySample (h : ℤ) (y : Fin 2 → ℤ) : Option QuarticReplicatedIndex → ℤ
  | none => y 1
  | some j => if j.1 = 0 then h else y 0

theorem quarticBinarySample_sum (h : ℤ) (y : Fin 2 → ℤ) :
    coordinateTranslatedInput quarticRepeatedCoordinates (quarticBinarySample h y) =
      quarticInput h (fun _ => y 0 + y 1) := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [coordinateTranslatedInput, quarticRepeatedCoordinates, quarticReplica,
      quarticBinarySample, quarticInput]

theorem quarticBinarySample_leaf (h : ℤ) (y : Fin 2 → ℤ) (v : Fin 3 → Fin 2) :
    binaryLeafInput quarticRepeatedCoordinates v (quarticBinarySample h y) =
      quarticInput h (fun j => y (v j)) := by
  have hf (z : Fin 2) : z = 0 ∨ z = 1 := by fin_cases z <;> simp
  rcases hf (v 0) with h0 | h0 <;>
    rcases hf (v 1) with h1 | h1 <;>
      rcases hf (v 2) with h2 | h2
  all_goals
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;>
      simp [binaryLeafInput, quarticRepeatedCoordinates, quarticReplica,
        quarticBinarySample, quarticInput, coordinateReplaceInput, coordinateReplaceIndex,
        Fin.tail, h0, h1, h2, Fin.ext_iff, -Fin.val_eq_zero_iff]

namespace NativeMultidegreeNilcharacter

theorem exists_quartic_binary_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun j (x : Fin 3 → ℤ) => W.eval j (quarticInput (x 0) (fun _ => x 1 + x 2)))
        (fun a : (Fin 3 → Fin 2) → Fin W.outputDim => fun x =>
          ∏ v : Fin 3 → Fin 2, W.eval (a v) (quarticInput (x 0) (fun j => x (v j).succ))) := by
  let := replicatedMixed_nonempty 3
  obtain ⟨C, hC, hexpand⟩ := exists_binary_assignment_equivalence quarticRepeatedCoordinates
  refine ⟨C, hC, ?_⟩
  intro p W
  have hnodup : quarticRepeatedCoordinates.Nodup := by decide
  let A : Option QuarticReplicatedIndex → ((Fin 3 → ℤ) →+ ℤ)
    | none => { toFun := fun x => x 2, map_zero' := rfl, map_add' := fun _ _ => rfl }
    | some j => if j.1 = 0 then
        { toFun := fun x => x 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
      else { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hA (x : Fin 3 → ℤ) : (fun j => A j x) = quarticBinarySample (x 0) (fun j => x j.succ) := by
    funext j
    cases j with
    | none => rfl
    | some j =>
      simp only [A, quarticBinarySample]
      split_ifs <;> rfl
  have E := (hexpand W hnodup).linearPullbackHom A
  change NativeIntegerVectorEquivalence (Fintype.card QuarticReplicatedIndex - 1) ((p + C) ^ C)
    (fun j (x : Fin 3 → ℤ) => W.eval j
      (coordinateTranslatedInput quarticRepeatedCoordinates (fun j => A j x)))
    (fun a : (Fin 3 → Fin 2) → Fin W.outputDim => fun x =>
      ∏ v : Fin 3 → Fin 2, W.eval (a v)
        (binaryLeafInput quarticRepeatedCoordinates v (fun j => A j x))) at E
  have h0 : (0 : Fin 2).succ = (1 : Fin 3) := rfl
  have h1 : (1 : Fin 2).succ = (2 : Fin 3) := rfl
  simpa only [hA, quarticBinarySample_sum, quarticBinarySample_leaf,
    replicatedMixed_card, Nat.reduceAdd, Nat.reduceSub, h0, h1] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticReflectionMatrix : Option QuarticReplicatedIndex → Fin 4 → ℤ
  | none => ![0, 1, 0, 0]
  | some j => if j.1 = 0 then ![1, 0, 0, 0]
    else if j.2.val = 0 then ![-1, -1, 0, 0]
    else if j.2.val = 1 then ![0, 0, 1, 0] else ![0, 0, 0, 1]

def quarticReflectionOffset (c : ℤ) : Option QuarticReplicatedIndex → ℤ
  | none => 0
  | some j => if j.1 = 0 then 0 else if j.2.val = 0 then c else 0

theorem quarticReflectionInput_sum (c : ℤ) (x : Fin 4 → ℤ) :
    coordinateAdditionInputs (quarticReplica 0)
      (integerAffineMap quarticReflectionMatrix (quarticReflectionOffset c) x) 0 =
        quarticInput (x 0) ![c - x 0, x 2, x 3] := by
  have hne : (⟨1, ⟨2, by decide⟩⟩ : QuarticReplicatedIndex) ≠ ⟨1, ⟨0, by decide⟩⟩ := by decide
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [coordinateAdditionInputs, integerAffineMap, quarticReflectionMatrix,
      quarticReflectionOffset, quarticReplica, quarticInput, Fin.sum_univ_four, hne]
  ring

theorem quarticReflectionInput_left (c : ℤ) (x : Fin 4 → ℤ) :
    coordinateAdditionInputs (quarticReplica 0)
      (integerAffineMap quarticReflectionMatrix (quarticReflectionOffset c) x) 1 =
        quarticInput (x 0) ![c - x 0 - x 1, x 2, x 3] := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [coordinateAdditionInputs, integerAffineMap, quarticReflectionMatrix,
      quarticReflectionOffset, quarticReplica, quarticInput, Fin.sum_univ_four]
  ring

theorem quarticReflectionInput_right (c : ℤ) (x : Fin 4 → ℤ) :
    coordinateAdditionInputs (quarticReplica 0)
      (integerAffineMap quarticReflectionMatrix (quarticReflectionOffset c) x) 2 =
        quarticInput (x 0) ![x 1, x 2, x 3] := by
  have hne : (⟨1, ⟨2, by decide⟩⟩ : QuarticReplicatedIndex) ≠ ⟨1, ⟨0, by decide⟩⟩ := by decide
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [coordinateAdditionInputs, integerAffineMap, quarticReflectionMatrix,
      quarticReflectionOffset, quarticReplica, quarticInput, Fin.sum_univ_four, hne]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_second_multilinearization :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) =
            W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (mixedSecondDifferenceVector (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1)))) := by
  obtain ⟨A, _, hmulti⟩ := exists_symmetric_multilinearization 3
  obtain ⟨B, _, hsecond⟩ := NativeIntegerVectorEquivalence.exists_second_difference_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, U, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨W, hdim, hsymm, E⟩ := hmulti (mixedCorrelationDegree 3)
    (by rw [Fin.sum_univ_two]; rfl) M
  have heq (x : Fin 2 → ℤ) : (fun j : QuarticReplicatedIndex => x j.1) =
      quarticInput (x 0) (fun _ => x 1) := by
    rw [quarticInput_diagonal]
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> rfl
  have E' : NativeIntegerVectorEquivalence 3 q M.eval
      (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) := by
    simpa only [heq] using E
  refine ⟨W.mono hqC, ?_, hsymm, E'.mono hqC, ?_⟩
  · exact hdim
  · rw [M.mixedSecondDifferenceWithShift_zero]
    exact (hsecond hq E').mono hrC

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def quarticPermutationWord (a : Fin 6) : QuarticTernaryAssignment :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]] a

theorem quarticPermutationWord_bijective (a : Fin 6) : Function.Bijective (quarticPermutationWord a) := by
  fin_cases a <;> decide

noncomputable def quarticWordPermutation (a : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (quarticPermutationWord a) (quarticPermutationWord_bijective a)

def quarticDoubleFirstWord (j : Fin 3) : QuarticTernaryAssignment :=
  fun i => if i = j then 2 else 1

def quarticDoubleSecondWord (j : Fin 3) : QuarticTernaryAssignment :=
  fun i => if i = j then 1 else 2

def quarticSurvivorClassMap : Fin 6 ⊕ (Fin 3 ⊕ Fin 3) → QuarticSurvivor
  | Sum.inl a => ⟨quarticPermutationWord a, by fin_cases a <;> decide⟩
  | Sum.inr (Sum.inl j) => ⟨quarticDoubleFirstWord j, by fin_cases j <;> decide⟩
  | Sum.inr (Sum.inr j) => ⟨quarticDoubleSecondWord j, by fin_cases j <;> decide⟩

theorem quarticSurvivorClassMap_bijective : Function.Bijective quarticSurvivorClassMap := by
  decide

noncomputable def quarticSurvivorClassEquiv : Fin 6 ⊕ (Fin 3 ⊕ Fin 3) ≃ QuarticSurvivor :=
  Equiv.ofBijective quarticSurvivorClassMap quarticSurvivorClassMap_bijective

theorem quartic_survivor_class_product (f : QuarticSurvivor → ℂ) :
    (∏ v, f v) =
      (∏ a : Fin 6, f (quarticSurvivorClassMap (Sum.inl a))) *
        ((∏ j : Fin 3, f (quarticSurvivorClassMap (Sum.inr (Sum.inl j)))) *
          ∏ j : Fin 3, f (quarticSurvivorClassMap (Sum.inr (Sum.inr j)))) := by
  calc
    _ = ∏ a : Fin 6 ⊕ (Fin 3 ⊕ Fin 3), f (quarticSurvivorClassEquiv a) :=
      (quarticSurvivorClassEquiv.prod_comp f).symm
    _ = _ := by simp only [Fintype.prod_sum_type]; rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticTerm {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (v : QuarticTernaryAssignment) (i : I) (x : Fin 4 → ℤ) : ℂ :=
  f i (quarticInput (x 0) (fun j => x (v j).succ))

noncomputable def quarticFaceVector {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (b : Fin 2) (a : QuarticBinaryAssignment → I) (x : Fin 4 → ℤ) : ℂ :=
  ∏ v, quarticTerm f (quarticBinaryWord b v) (a v) x

noncomputable def quarticCommonVector {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : (QuarticBinaryAssignment → I) × (QuarticBinaryAssignment → I)) (x : Fin 4 → ℤ) : ℂ :=
  quarticFaceVector f 0 a.1 x * quarticFaceVector f 1 a.2 x

noncomputable def quarticSurvivorVector {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : QuarticSurvivor → I) (x : Fin 4 → ℤ) : ℂ :=
  ∏ v, quarticTerm f v.val (a v) x

theorem quarticFaceVector_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (b : Fin 2) (x : Fin 4 → ℤ) :
    ∑ a, ‖quarticFaceVector f b a x‖ ^ 2 = 1 := by
  change (∑ a : QuarticBinaryAssignment → I,
    ‖∏ v : QuarticBinaryAssignment, quarticTerm f (quarticBinaryWord b v) (a v) x‖ ^ 2) = 1
  exact finite_product_unit_vector
    (fun (v : QuarticBinaryAssignment) (i : I) => quarticTerm f (quarticBinaryWord b v) i x)
    (fun _ => hf _)

theorem quarticCommonVector_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (x : Fin 4 → ℤ) :
    ∑ a, ‖quarticCommonVector f a x‖ ^ 2 = 1 := by
  simp only [quarticCommonVector, Fintype.sum_prod_type, norm_mul, mul_pow,
    ← Finset.mul_sum, quarticFaceVector_unit f hf, mul_one]

theorem quarticSurvivorVector_unit {I : Type*} [Fintype I] (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (hf : ∀ x, ∑ i, ‖f i x‖ ^ 2 = 1) (x : Fin 4 → ℤ) :
    ∑ a, ‖quarticSurvivorVector f a x‖ ^ 2 = 1 := by
  change (∑ a : QuarticSurvivor → I,
    ‖∏ v : QuarticSurvivor, quarticTerm f v.val (a v) x‖ ^ 2) = 1
  exact finite_product_unit_vector
    (fun (v : QuarticSurvivor) (i : I) => quarticTerm f v.val i x) (fun _ => hf _)

def quarticFaceCoordinate (b : Fin 2) (j : Fin 3) : Fin 4 :=
  if j = 0 then 0 else if j = 1 then 1 else b.succ.succ

theorem quarticFaceCoordinate_word (b : Fin 2) (v : QuarticBinaryAssignment) (j : Fin 3) :
    quarticFaceCoordinate b (v j).succ = (quarticBinaryWord b v j).succ := by
  generalize h : v j = z
  fin_cases z <;> fin_cases b <;> simp [quarticFaceCoordinate, quarticBinaryWord, h]

def quarticPartitionCoordinate {I : Type*}
    (a : ((QuarticBinaryAssignment → I) × (QuarticBinaryAssignment → I)) × (QuarticSurvivor → I)) :
    (Fin 2 × QuarticBinaryAssignment) ⊕ QuarticSurvivor → I
  | Sum.inl (b, v) => if b = 0 then a.1.1 v else a.1.2 v
  | Sum.inr v => a.2 v

noncomputable def quarticAssignmentReindex {I : Type*}
    (a : ((QuarticBinaryAssignment → I) × (QuarticBinaryAssignment → I)) × (QuarticSurvivor → I)) :
    I × (QuarticTernaryAssignment → I) :=
  (quarticPartitionCoordinate a (quarticAssignmentEquiv.symm none),
    fun v => quarticPartitionCoordinate a (quarticAssignmentEquiv.symm (some v)))

theorem quartic_product_reindex {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : ((QuarticBinaryAssignment → I) × (QuarticBinaryAssignment → I)) × (QuarticSurvivor → I))
    (x : Fin 4 → ℤ) :
    f (quarticAssignmentReindex a).1 (quarticInput (x 0) (fun _ => x 1)) *
        (∏ v, quarticTerm f v ((quarticAssignmentReindex a).2 v) x) =
      quarticCommonVector f a.1 x * quarticSurvivorVector f a.2 x := by
  have h := quartic_assignment_product (fun v i => quarticTerm f v i x) (quarticPartitionCoordinate a)
  simpa [quarticAssignmentReindex, quarticPartitionCoordinate, quarticTerm,
    quarticCommonVector, quarticFaceVector, quarticSurvivorVector] using h

noncomputable def quarticSecondVector {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ)
    (a : (I × I) × (I × I)) (x : Fin 4 → ℤ) : ℂ :=
  (f a.1.1 (quarticInput (x 0) (fun _ => x 1)) *
    star (f a.1.2 (quarticInput (x 0) (fun _ => x 1 + x 2)))) *
    star (f a.2.1 (quarticInput (x 0) (fun _ => x 1 + x 3)) *
      star (f a.2.2 (quarticInput (x 0) (fun _ => x 1 + x 2 + x 3))))

theorem quarticSecondVector_eq {I : Type*} (f : I → (QuarticReplicatedIndex → ℤ) → ℂ) :
    mixedSecondDifferenceVector (fun i x => f i (quarticInput (x 0) (fun _ => x 1))) =
      quarticSecondVector f := by
  funext a x
  change (f a.1.1 (quarticInput (x 0) (fun _ => x 1 + 0)) *
    star (f a.1.2 (quarticInput (x 0) (fun _ => x 1 + x 2)))) *
    star (f a.2.1 (quarticInput (x 0) (fun _ => x 1 + x 3)) *
      star (f a.2.2 (quarticInput (x 0) (fun _ => x 1 + (x 2 + x 3))))) = _
  simp only [quarticSecondVector, add_zero, add_assoc]

namespace NativeMultidegreeNilcharacter

theorem exists_quartic_face_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p) (b : Fin 2),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 4 → ℤ) => W.eval i
          (quarticInput (x 0) (fun _ => x 1 + x b.succ.succ)))
        (quarticFaceVector W.eval b) := by
  obtain ⟨C, hC, hexpand⟩ := exists_quartic_binary_expansion
  refine ⟨C, hC, ?_⟩
  intro p W b
  have E := (hexpand W).coordinatePullback (quarticFaceCoordinate b)
  change NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
    (fun i (x : Fin 4 → ℤ) => W.eval i (quarticInput (x (quarticFaceCoordinate b 0))
      (fun _ => x (quarticFaceCoordinate b 1) + x (quarticFaceCoordinate b 2))))
    (fun a : QuarticBinaryAssignment → Fin W.outputDim => fun x =>
      ∏ v : QuarticBinaryAssignment, W.eval (a v) (quarticInput (x (quarticFaceCoordinate b 0))
        (fun j => x (quarticFaceCoordinate b (v j).succ)))) at E
  have h0 : quarticFaceCoordinate b 0 = 0 := rfl
  have h1 : quarticFaceCoordinate b 1 = 1 := rfl
  have h2 : quarticFaceCoordinate b 2 = b.succ.succ := rfl
  change NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
    (fun i (x : Fin 4 → ℤ) => W.eval i
      (quarticInput (x 0) (fun _ => x 1 + x b.succ.succ)))
    (fun a : QuarticBinaryAssignment → Fin W.outputDim => fun x =>
      ∏ v : QuarticBinaryAssignment, W.eval (a v)
        (quarticInput (x 0) (fun j => x (quarticBinaryWord b v j).succ)))
  simpa only [h0, h1, h2, quarticFaceCoordinate_word] using E

theorem exists_quartic_diagonal_self_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (fun i (x : Fin 4 → ℤ) => W.eval i (quarticInput (x 0) (fun _ => x 1)))
        (fun i (x : Fin 4 → ℤ) => W.eval i (quarticInput (x 0) (fun _ => x 1))) := by
  let := replicatedMixed_nonempty 3
  obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := QuarticReplicatedIndex)
  refine ⟨C, hC, ?_⟩
  intro p W
  have E := (hself W).coordinatePullback (fun j => if j.1 = 0 then (0 : Fin 4) else 1)
  have hinput (x : Fin 4 → ℤ) : (fun j : QuarticReplicatedIndex => x (if j.1 = 0 then 0 else 1)) =
      quarticInput (x 0) (fun _ => x 1) := by
    funext j
    by_cases h : j.1 = 0 <;> simp [quarticInput, h]
  simpa only [hinput, replicatedMixed_card, Nat.reduceAdd, Nat.reduceSub] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def quarticFirstReplica : QuarticReplicatedIndex := ⟨0, ⟨0, by decide⟩⟩

def quarticAllCoordinates : List QuarticReplicatedIndex :=
  [quarticFirstReplica, quarticReplica 0, quarticReplica 1, quarticReplica 2]

def quarticDiagonalSampleInput (x : Fin 2 → ℤ) : Option QuarticReplicatedIndex → ℤ
  | none => x 0
  | some _ => x 1

def quarticDiagonalCorner (v : Fin 4 → Fin 2) (x : Fin 2 → ℤ) : QuarticReplicatedIndex → ℤ :=
  quarticInput (x (v 0).rev) (fun j => x (v j.succ).rev)

theorem quarticDiagonalCorner_zero (x : Fin 2 → ℤ) :
    quarticDiagonalCorner (fun _ => 0) x = fun _ => x 1 := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;> rfl

theorem quarticDiagonalSample_sum (x : Fin 2 → ℤ) :
    coordinateTranslatedInput quarticAllCoordinates (quarticDiagonalSampleInput x) =
      fun _ => x 1 + x 0 := by
  funext j
  rcases j with ⟨j, k⟩
  fin_cases j <;> fin_cases k <;>
    simp [coordinateTranslatedInput, quarticAllCoordinates, quarticFirstReplica,
      quarticReplica, quarticDiagonalSampleInput]

theorem quarticDiagonalSample_leaf (v : Fin 4 → Fin 2) (x : Fin 2 → ℤ) :
    binaryLeafInput quarticAllCoordinates v (quarticDiagonalSampleInput x) =
      quarticDiagonalCorner v x := by
  have hf (z : Fin 2) : z = 0 ∨ z = 1 := by fin_cases z <;> simp
  rcases hf (v 0) with h0 | h0 <;>
    rcases hf (v 1) with h1 | h1 <;>
      rcases hf (v 2) with h2 | h2 <;>
        rcases hf (v 3) with h3 | h3
  all_goals
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;>
      simp [binaryLeafInput, quarticAllCoordinates, quarticFirstReplica, quarticReplica,
        quarticDiagonalSampleInput, quarticDiagonalCorner, quarticInput,
        coordinateReplaceInput, coordinateReplaceIndex, Fin.tail,
        h0, h1, h2, h3, Fin.ext_iff, -Fin.val_eq_zero_iff]

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)

noncomputable def quarticDiagonalTensor
    (a : (Fin 4 → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∏ v, W.eval (a v) (quarticDiagonalCorner v x)

theorem quarticDiagonalTensor_norm
    (a : (Fin 4 → Fin 2) → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.quarticDiagonalTensor a x‖ ≤ 1 := by
  rw [quarticDiagonalTensor, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem quarticDiagonalTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : (Fin 4 → Fin 2) → Fin W.outputDim, ‖W.quarticDiagonalTensor a x‖ ^ 2 = 1 := by
  simp only [quarticDiagonalTensor, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : Fin 4 → Fin 2, ∑ a : Fin W.outputDim, ‖W.eval a (quarticDiagonalCorner v x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_survivor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 3 ((p + C) ^ C)
        (quarticSecondVector W.eval) (quarticSurvivorVector W.eval) := by
  obtain ⟨A, _, hface⟩ := exists_quartic_face_expansion
  obtain ⟨B, _, hternary⟩ := exists_quartic_ternary_expansion
  obtain ⟨D, _, hself⟩ := exists_quartic_diagonal_self_equivalence
  obtain ⟨T, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  obtain ⟨F, _, hcancel⟩ := NativeIntegerVectorEquivalence.exists_cancel_left_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A + (X + Polynomial.C B) ^ B +
    (X + Polynomial.C D) ^ D + 28 * X + 2
  let R := Q + (Q + Polynomial.C T) ^ T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C F) ^ F)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A + (p + B) ^ B + (p + D) ^ D + 28 * p + 2
  let t := (q + T) ^ T
  let r := q + t
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hB : 0 ≤ (p + B) ^ B := by positivity
  have hD : 0 ≤ (p + D) ^ D := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hAq : (p + A) ^ A ≤ q := by dsimp [q]; linarith
  have hBq : (p + B) ^ B ≤ q := by dsimp [q]; linarith
  have hDq : (p + D) ^ D ≤ q := by dsimp [q]; linarith
  have h28q : 28 * p ≤ q := by dsimp [q]; linarith
  have hqr : q ≤ r := by dsimp [r]; linarith
  have htr : t ≤ r := by dsimp [r]; linarith
  have h12r : 12 * p ≤ r := by linarith
  have h28r : 28 * p ≤ r := h28q.trans hqr
  have hcost : (r + F) ^ F ≤ (p + C) ^ C := by
    have h := hbudget p hp
    have hsum : r + (r + F) ^ F ≤ (p + C) ^ C := by
      simpa [X, Q, R, q, t, r, Polynomial.eval₂_pow] using h
    linarith
  let I := Fin W.outputDim
  let J := QuarticBinaryAssignment → I
  let L := QuarticSurvivor → I
  have hI : (Fintype.card I : ℝ) ≤ Real.exp p := by
    simpa only [I, Fintype.card_fin] using W.output_bound
  have h8 : (Fintype.card J : ℝ) ≤ Real.exp (8 * p) := by
    simpa only [J, I, Fintype.card_fun, Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat] using
      (function_card_le_exp (A := QuarticBinaryAssignment) hI)
  have h12 : (Fintype.card L : ℝ) ≤ Real.exp (12 * p) := by
    simpa only [L, I, quarticSurvivor_card, Nat.cast_ofNat] using
      (function_card_le_exp (A := QuarticSurvivor) hI)
  have h16 : (Fintype.card (J × J) : ℝ) ≤ Real.exp (16 * p) := by
    calc
      _ ≤ Real.exp (2 * (8 * p)) := card_product_le_exp_two h8 h8
      _ = _ := congrArg Real.exp (by ring)
  have h28 : (Fintype.card ((J × J) × L) : ℝ) ≤ Real.exp (28 * p) := by
    calc
      _ = (Fintype.card (J × J) : ℝ) * (Fintype.card L : ℝ) := by
        simp only [Fintype.card_prod, Nat.cast_mul]
      _ ≤ Real.exp (16 * p) * Real.exp (12 * p) :=
        mul_le_mul h16 h12 (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have E : NativeIntegerVectorEquivalence 3 t
      (fun a : I × I => fun x : Fin 4 → ℤ =>
        W.eval a.1 (quarticInput (x 0) (fun _ => x 1 + x 2)) *
          W.eval a.2 (quarticInput (x 0) (fun _ => x 1 + x 3)))
      (quarticCommonVector W.eval) :=
    htensor hq ((hface W 0).mono hAq) ((hface W 1).mono hAq)
  have H := htensor hq ((hself W).mono hDq) ((hternary W).mono hBq)
  have H' : NativeIntegerVectorEquivalence 3 r
      (fun a : I × I => fun x : Fin 4 → ℤ =>
        W.eval a.1 (quarticInput (x 0) (fun _ => x 1)) *
          W.eval a.2 (quarticInput (x 0) (fun _ => x 1 + x 2 + x 3)))
      (fun a : (J × J) × L => fun x =>
        quarticCommonVector W.eval a.1 x * quarticSurvivorVector W.eval a.2 x) := by
    apply H.of_coordinate_maps _ _ id quarticAssignmentReindex
      (fun _ _ => rfl) _ (H.left_dimension.trans (Real.exp_le_exp.mpr htr))
      (h28.trans (Real.exp_le_exp.mpr h28r)) htr
    intro a x
    exact (quartic_product_reindex W.eval a x).symm
  have K := hcancel hr (E.mono htr) H' (quarticCommonVector_unit W.eval W.unit_eval)
    (h12.trans (Real.exp_le_exp.mpr h12r))
  apply K.conjugate.of_coordinate_maps _ _
    (fun a : (I × I) × (I × I) => ((a.1.2, a.2.1), (a.1.1, a.2.2))) id
    _ _ (K.left_dimension.trans (Real.exp_le_exp.mpr hcost))
    (K.right_dimension.trans (Real.exp_le_exp.mpr hcost)) hcost
  · intro a x
    simp only [quarticSecondVector, star_mul, star_star]
    ring
  · intro a x
    exact (star_star (quarticSurvivorVector W.eval a x)).symm

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_quartic_survivor_multilinearization :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 3) p),
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) ((p + C) ^ C),
        W.dim ≤ 16 * M.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) =
            W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) M.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 ((p + C) ^ C) (M.mixedSecondDifferenceWithShift 0)
          (quarticSurvivorVector W.eval) := by
  obtain ⟨A, _, hmulti⟩ := exists_quartic_second_multilinearization
  obtain ⟨B, _, hsurvive⟩ := exists_quartic_survivor_equivalence
  obtain ⟨D, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + R + 2 + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro p M
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  let s := q + r + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hqs : q ≤ s := by dsimp [s]; linarith
  have hrs : r ≤ s := by dsimp [s]; linarith
  have hD : 0 ≤ (s + D) ^ D := by positivity
  have htotal : q + (s + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, s, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hDC : (s + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨W, hdim, hsymm, Ebase, Esecond⟩ := hmulti M
  have E : NativeIntegerVectorEquivalence 3 q (M.mixedSecondDifferenceWithShift 0)
      (quarticSecondVector W.eval) := by
    simpa only [quarticSecondVector_eq] using Esecond
  have hunit (x : Fin 4 → ℤ) : ∑ a, ‖quarticSecondVector W.eval a x‖ ^ 2 = 1 := by
    simp only [quarticSecondVector, Fintype.sum_prod_type, norm_mul, norm_star,
      mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
  have H := htrans hs (E.mono hqs) ((hsurvive W).mono hrs) hunit
  exact ⟨W.mono hqC, hdim, hsymm, Ebase.mono hqC, H.mono hDC⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
