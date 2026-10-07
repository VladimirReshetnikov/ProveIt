import Mathlib.Data.Fin.Tuple.Basic
import OAI.Combinatorics.Progressions.Geometry.NativeFiniteSumCoordinate
import OAI.Combinatorics.Progressions.Geometry.NativeTernaryCoordinate
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerEquivalenceFiniteFamily

namespace OAI

section

namespace Erdos3

variable {σ I : Type*} [DecidableEq σ]

noncomputable def firstTranslationCoordinate : (l : List σ) → BinaryTensorIndex I l.length → I
  | [], a => a
  | _ :: l, a => firstTranslationCoordinate l a.1

noncomputable def translationExpansionRemainder (f : I → (σ → ℤ) → ℂ) :
    (l : List σ) → BinaryTensorIndex I l.length → (Option σ → ℤ) → ℂ
  | [], _, _ => 1
  | i :: l, a, x => translationExpansionRemainder f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_factor (f : I → (σ → ℤ) → ℂ)
    (l : List σ) (a : BinaryTensorIndex I l.length) (x : Option σ → ℤ) :
    coordinateTranslationExpansion f l a x =
      f (firstTranslationCoordinate l a) (fun j => x (some j)) *
        translationExpansionRemainder f l a x := by
  induction l generalizing x with
  | nil => exact (mul_one _).symm
  | cons i l ih =>
    change coordinateTranslationExpansion f l a.1 x *
      coordinateTranslationExpansion f l a.2 (coordinateReplaceInput i x) = _
    rw [ih]
    exact mul_assoc _ _ _

theorem coordinateTranslationExpansion_norm_le_one (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (l : List σ)
    (a : BinaryTensorIndex I l.length) (x : Option σ → ℤ) :
    ‖coordinateTranslationExpansion f l a x‖ ≤ 1 := by
  induction l generalizing x with
  | nil => exact hf _ _
  | cons i l ih =>
    rw [coordinateTranslationExpansion, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ih _ _)).trans (ih _ _)

theorem translationExpansionRemainder_norm_le_one (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (l : List σ)
    (a : BinaryTensorIndex I l.length) (x : Option σ → ℤ) :
    ‖translationExpansionRemainder f l a x‖ ≤ 1 := by
  induction l generalizing x with
  | nil => exact (norm_one : ‖(1 : ℂ)‖ = 1).le
  | cons i l ih =>
    rw [translationExpansionRemainder, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ih _ _)).trans
      (coordinateTranslationExpansion_norm_le_one f hf l _ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def ternaryIndexOfFunction {I : Type*} : (n : ℕ) → ((Fin n → Fin 3) → I) → TernaryTensorIndex I n
  | 0, a => a Fin.elim0
  | n + 1, a => (ternaryIndexOfFunction n (fun v => a (Fin.cons 0 v)),
      ternaryIndexOfFunction n (fun v => a (Fin.cons 1 v)),
      ternaryIndexOfFunction n (fun v => a (Fin.cons 2 v)))

def ternaryLeafInput {σ : Type*} [DecidableEq σ] :
    (l : List σ) → (Fin l.length → Fin 3) → ((Fin 3 × σ) → ℤ) → (σ → ℤ)
  | [], _, x => fun j => x (0, j)
  | i :: l, v, x => ternaryLeafInput l (Fin.tail v) (ternaryReplaceInput i (v 0) x)

theorem ternaryReplaceInput_zero {σ : Type*} [DecidableEq σ] (i : σ) (x : (Fin 3 × σ) → ℤ) :
    ternaryReplaceInput i 0 x = x := by
  funext j
  simp only [ternaryReplaceInput, ternaryReplaceIndex]
  split_ifs with hj
  · rw [hj]
  · rfl

theorem prod_fin_succ_function {n m : ℕ} (f : (Fin (n + 1) → Fin m) → ℂ) :
    (∏ v, f v) = ∏ a : Fin m, ∏ v : Fin n → Fin m, f (Fin.cons a v) := by
  calc
    _ = ∏ a : Fin m × (Fin n → Fin m), f (Fin.cons a.1 a.2) :=
      ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin m)).prod_comp f).symm
    _ = _ := Fintype.prod_prod_type _

theorem ternaryCoordinateExpansion_leaves {σ I : Type*} [DecidableEq σ]
    (f : I → (σ → ℤ) → ℂ) (l : List σ)
    (a : (Fin l.length → Fin 3) → I) (x : (Fin 3 × σ) → ℤ) :
    ternaryCoordinateExpansion f l (ternaryIndexOfFunction l.length a) x =
      ∏ v : Fin l.length → Fin 3, f (a v) (ternaryLeafInput l v x) := by
  induction l generalizing x with
  | nil =>
    change f (a Fin.elim0) (fun j => x (0, j)) =
      ∏ v : Fin 0 → Fin 3, f (a v) (fun j => x (0, j))
    rw [Fintype.prod_unique]
    exact congrArg (fun v => f (a v) (fun j => x (0, j))) (by funext j; exact Fin.elim0 j)
  | cons i l ih =>
    simp only [List.length_cons, ternaryCoordinateExpansion, ternaryIndexOfFunction, ih,
      prod_fin_succ_function, Fin.prod_univ_three, ternaryLeafInput,
      Fin.cons_zero, Fin.tail_cons, ternaryReplaceInput_zero, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def binaryIndexOfFunction {I : Type*} : (n : ℕ) → ((Fin n → Fin 2) → I) → BinaryTensorIndex I n
  | 0, a => a Fin.elim0
  | n + 1, a => (binaryIndexOfFunction n (fun v => a (Fin.cons 0 v)),
      binaryIndexOfFunction n (fun v => a (Fin.cons 1 v)))

def binaryLeafInput {σ : Type*} [DecidableEq σ] :
    (l : List σ) → (Fin l.length → Fin 2) → (Option σ → ℤ) → (σ → ℤ)
  | [], _, x => fun j => x (some j)
  | i :: l, v, x => binaryLeafInput l (Fin.tail v)
      (if v 0 = 0 then x else coordinateReplaceInput i x)

theorem coordinateTranslationExpansion_leaves {σ I : Type*} [DecidableEq σ]
    (f : I → (σ → ℤ) → ℂ) (l : List σ)
    (a : (Fin l.length → Fin 2) → I) (x : Option σ → ℤ) :
    coordinateTranslationExpansion f l (binaryIndexOfFunction l.length a) x =
      ∏ v : Fin l.length → Fin 2, f (a v) (binaryLeafInput l v x) := by
  induction l generalizing x with
  | nil =>
    change f (a Fin.elim0) (fun j => x (some j)) =
      ∏ v : Fin 0 → Fin 2, f (a v) (fun j => x (some j))
    rw [Fintype.prod_unique]
    exact congrArg (fun v => f (a v) (fun j => x (some j))) (by funext j; exact Fin.elim0 j)
  | cons i l ih =>
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [List.length_cons, coordinateTranslationExpansion, binaryIndexOfFunction, ih,
      prod_fin_succ_function, Fin.prod_univ_two, binaryLeafInput,
      Fin.cons_zero, Fin.tail_cons, ↓reduceIte, h10]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ] {n : ℕ}

def finiteChoiceCoordinateInput (l : List σ) (x : (Fin (n + 1) × σ) → ℤ) (j : σ) : ℤ :=
  if j ∈ l then ∑ a : Fin (n + 1), x (a, j) else x (0, j)

def finiteChoiceCoordinateHom (l : List σ) (j : σ) : (((Fin (n + 1) × σ) → ℤ) →+ ℤ) where
  toFun x := finiteChoiceCoordinateInput l x j
  map_zero' := by simp [finiteChoiceCoordinateInput]
  map_add' x y := by
    simp only [finiteChoiceCoordinateInput, Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> rfl

def finiteChoiceReplaceIndex (i : σ) (a : Fin (n + 1)) (j : Fin (n + 1) × σ) : Fin (n + 1) × σ :=
  if j = (0, i) then (a, i) else j

def finiteChoiceReplaceInput (i : σ) (a : Fin (n + 1))
    (x : (Fin (n + 1) × σ) → ℤ) : (Fin (n + 1) × σ) → ℤ :=
  fun j => x (finiteChoiceReplaceIndex i a j)

theorem finiteChoiceCoordinateInput_replace (l : List σ) (i : σ) (hi : i ∉ l)
    (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) =
      Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hi]
  · simp [finiteChoiceCoordinateInput, finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj]

theorem finiteChoiceCoordinateInput_cons (l : List σ) (i : σ)
    (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceCoordinateInput (i :: l) x = Function.update (finiteChoiceCoordinateInput l x) i
      (∑ a : Fin (n + 1), x (a, i)) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [finiteChoiceCoordinateInput]
  · simp [finiteChoiceCoordinateInput, hj]

def finiteChoiceLeafInput : (l : List σ) → (Fin l.length → Fin (n + 1)) →
    ((Fin (n + 1) × σ) → ℤ) → σ → ℤ
  | [], _, x => fun j => x (0, j)
  | i :: l, v, x => finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x)

noncomputable def finiteChoiceExpansion (f : I → (σ → ℤ) → ℂ) (l : List σ)
    (a : (Fin l.length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) : ℂ :=
  ∏ v : Fin l.length → Fin (n + 1), f (a v) (finiteChoiceLeafInput l v x)

theorem finiteChoiceExpansion_cons (f : I → (σ → ℤ) → ℂ) (l : List σ) (i : σ)
    (a : (Fin (i :: l).length → Fin (n + 1)) → I) (x : (Fin (n + 1) × σ) → ℤ) :
    finiteChoiceExpansion f (i :: l) a x = ∏ j : Fin (n + 1),
      finiteChoiceExpansion f l (fun v => a (Fin.cons j v)) (finiteChoiceReplaceInput i j x) := by
  simp only [finiteChoiceExpansion, List.length_cons, prod_fin_succ_function, finiteChoiceLeafInput,
    Fin.cons_zero, Fin.tail_cons]

theorem finiteChoiceExpansion_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (l : List σ) (x : (Fin (n + 1) × σ) → ℤ) :
    ∑ a : (Fin l.length → Fin (n + 1)) → I, ‖finiteChoiceExpansion f l a x‖ ^ 2 = 1 := by
  simp only [finiteChoiceExpansion, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ v : Fin l.length → Fin (n + 1), ∑ i : I, ‖f i (finiteChoiceLeafInput l v x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [hf, Finset.prod_const_one]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_translation_expansion_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k x => W.eval k (coordinateTranslatedInput l x))
        (coordinateTranslationExpansion W.eval l) := by
  induction l with
  | nil =>
    obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
    refine ⟨C, hC, ?_⟩
    intro p W _
    have E := (hself W).coordinatePullback (some : σ → Option σ)
    have hinput (x : Option σ → ℤ) :
        coordinateTranslatedInput [] x = fun j => x (some j) := by
      funext j
      simp [coordinateTranslatedInput]
    simp only [hinput, coordinateTranslationExpansion]
    convert E using 1 <;> rfl
  | cons i l ih =>
    obtain ⟨a, _, hprevious⟩ := ih
    obtain ⟨b, _, hstep⟩ := exists_coordinate_translation_equivalence (σ := σ)
    obtain ⟨c, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
    obtain ⟨d, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
    let X : Polynomial ℕ := Polynomial.X
    let A := (X + Polynomial.C a) ^ a
    let B := (X + Polynomial.C b) ^ b
    let T := (A + Polynomial.C c) ^ c
    let Q := B + T + 2
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C d) ^ d)
    refine ⟨C, hC, ?_⟩
    intro p W hl
    have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
    let q := (p + a) ^ a
    let r := (q + c) ^ c
    let t := (p + b) ^ b + r + 2
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hb : 0 ≤ (p + b) ^ b := by positivity
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hbt : (p + b) ^ b ≤ t := by dsimp [t]; linarith only [hr]
    have hrt : r ≤ t := by dsimp [t]; linarith only [hb]
    have E := hprevious W hl.tail
    have F := htensor hq E (E.coordinatePullback (coordinateReplaceIndex i))
    have F' : NativeIntegerVectorEquivalence (Fintype.card σ - 1) r
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x)))
        (coordinateTranslationExpansion W.eval (i :: l)) := F
    have hunit (x : Option σ → ℤ) :
        ∑ k : Fin W.outputDim × Fin W.outputDim,
          ‖W.eval k.1 (coordinateTranslatedInput l x) *
            W.eval k.2 (coordinateTranslatedInput l (coordinateReplaceInput i x))‖ ^ 2 = 1 := by
      simp only [Fintype.sum_prod_type, norm_mul, mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]
    have R := htrans ht ((hstep W l i (List.nodup_cons.mp hl).1).mono hbt) (F'.mono hrt) hunit
    have hcost : (t + d) ^ d ≤ (p + C) ^ C := by
      simpa [X, A, B, T, Q, q, r, t, Polynomial.eval₂_pow] using hbudget p hp
    exact R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_finite_assignment_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (n : ℕ) (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun k (x : (Fin (n + 1) × σ) → ℤ) => W.eval k (finiteChoiceCoordinateInput l x))
        (finiteChoiceExpansion W.eval l) := by
  induction l with
  | nil =>
      obtain ⟨C, hC, hself⟩ := exists_integer_self_equivalence (σ := σ)
      refine ⟨C, hC, ?_⟩
      intro p W _
      have E := (hself W).coordinatePullback (fun j => ((0 : Fin (n + 1)), j))
      apply E.of_coordinate_maps _ _ id (fun a => a Fin.elim0)
        (fun _ _ => rfl) _ E.left_dimension _ le_rfl
      · intro a x
        change (∏ v : Fin 0 → Fin (n + 1), W.eval (a v) (fun j => x (0, j))) =
          W.eval (a Fin.elim0) (fun j => x (0, j))
        rw [Fintype.prod_unique]
        exact congrArg (fun v => W.eval (a v) (fun j => x (0, j))) (by
          funext j
          exact Fin.elim0 j)
      · simpa only [Fintype.card_fun, Fintype.card_fin, List.length_nil, pow_zero, pow_one]
          using E.right_dimension
  | cons i l ih =>
      obtain ⟨A, _, hprevious⟩ := ih
      obtain ⟨B, _, hstep⟩ := exists_finite_sum_coordinate_equivalence (σ := σ) n
      obtain ⟨D, _, hproduct⟩ := NativeIntegerVectorEquivalence.exists_fin_product_budget (n + 1)
      obtain ⟨F, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
      let X : Polynomial ℕ := Polynomial.X
      let Q := (X + Polynomial.C A) ^ A
      let T := (Q + Polynomial.C D) ^ D
      let R := (X + Polynomial.C B) ^ B + T
      obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
        ((R + Polynomial.C F) ^ F + Polynomial.C ((n + 1) ^ (l.length + 1)) * X + X)
      refine ⟨C, hC, ?_⟩
      intro p W hl
      have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
      let q := (p + A) ^ A
      let t := (q + D) ^ D
      let r := (p + B) ^ B + t
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have ht : 0 ≤ t := by dsimp [t]; positivity
      have hB : 0 ≤ (p + B) ^ B := by positivity
      have hr : 0 ≤ r := by dsimp [r]; linarith
      have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
      have htr : t ≤ r := by dsimp [r]; linarith
      have hsum : (r + F) ^ F + ((n + 1) ^ (l.length + 1) : ℕ) * p + p ≤ (p + C) ^ C := by
        simpa [X, Q, T, R, q, t, r, Polynomial.eval₂_pow] using hbudget p hp
      have hpow : 0 ≤ (r + F) ^ F := by positivity
      have hnp : 0 ≤ ((n + 1) ^ (l.length + 1) : ℕ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hFC : (r + F) ^ F ≤ (p + C) ^ C := by linarith
      have hpC : p ≤ (p + C) ^ C := by linarith
      have hnC : ((n + 1) ^ (l.length + 1) : ℕ) * p ≤ (p + C) ^ C := by linarith
      let P : (σ ⊕ Fin (n + 1)) → (((Fin (n + 1) × σ) → ℤ) →+ ℤ) := fun j =>
        match j with
        | Sum.inl j => finiteChoiceCoordinateHom l j
        | Sum.inr a =>
          { toFun := fun x => x (a, i)
            map_zero' := rfl
            map_add' := fun _ _ => rfl }
      have hleft (x : (Fin (n + 1) × σ) → ℤ) :
          finiteSumCoordinateInput i (fun j => P j x) = finiteChoiceCoordinateInput (i :: l) x := by
        change Function.update (finiteChoiceCoordinateInput l x) i
          (∑ a : Fin (n + 1), x (a, i)) = _
        exact (finiteChoiceCoordinateInput_cons l i x).symm
      have hright (a : Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) :
          finiteTermCoordinateInput i a (fun j => P j x) =
            finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i a x) := by
        change Function.update (finiteChoiceCoordinateInput l x) i (x (a, i)) = _
        exact (finiteChoiceCoordinateInput_replace l i (List.nodup_cons.mp hl).1 a x).symm
      have E₀ : NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + B) ^ B)
          (fun k x => W.eval k (finiteChoiceCoordinateInput (i :: l) x))
          (fun a : Fin (n + 1) → Fin W.outputDim => fun x => ∏ j,
            W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))) := by
        have E := (hstep W i).linearPullbackHom P
        simpa only [hleft, hright] using E
      have E := hprevious W hl.tail
      have E₁ := hproduct
        (fun j k x => W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x)))
        (fun j a x => finiteChoiceExpansion W.eval l a (finiteChoiceReplaceInput i j x))
        hq E.left_dimension E.right_dimension
        (fun j => E.coordinatePullback (finiteChoiceReplaceIndex i j))
      have hunit (x : (Fin (n + 1) × σ) → ℤ) :
          ∑ a : Fin (n + 1) → Fin W.outputDim,
            ‖∏ j, W.eval (a j) (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 = 1 := by
        simp only [norm_prod, ← Finset.prod_pow]
        calc
          _ = ∏ j : Fin (n + 1), ∑ k : Fin W.outputDim,
              ‖W.eval k (finiteChoiceCoordinateInput l (finiteChoiceReplaceInput i j x))‖ ^ 2 :=
            (Fintype.prod_sum _).symm
          _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]
      have H := htrans hr (E₀.mono hBr) (E₁.mono htr) hunit
      have hdim : (Fintype.card ((Fin (i :: l).length → Fin (n + 1)) → Fin W.outputDim) : ℝ) ≤
          Real.exp ((p + C) ^ C) := by
        simp only [Fintype.card_fun, Fintype.card_fin, List.length_cons, Nat.cast_pow]
        calc
          _ ≤ Real.exp p ^ ((n + 1) ^ (l.length + 1)) :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
          _ = Real.exp (((n + 1) ^ (l.length + 1) : ℕ) * p) :=
            (Real.exp_nat_mul p ((n + 1) ^ (l.length + 1))).symm
          _ ≤ _ := Real.exp_le_exp.mpr hnC
      apply H.of_coordinate_maps _ _ id (fun a j v => a (Fin.cons j v))
        (fun _ _ => rfl) _ _ hdim hFC
      · intro a x
        exact finiteChoiceExpansion_cons W.eval l i a x
      · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def mixedTranslationCoordinates (s : ℕ) :
    List (ReplicatedIndex (mixedCorrelationDegree s)) :=
  (Finset.univ.filter (fun j : ReplicatedIndex (mixedCorrelationDegree s) => j.1 = 1)).toList

@[simp] theorem mem_mixedTranslationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedTranslationCoordinates s ↔ j.1 = 1 := by
  simp [mixedTranslationCoordinates]

theorem mixedTranslationCoordinates_nodup (s : ℕ) : (mixedTranslationCoordinates s).Nodup :=
  Finset.nodup_toList _

def mixedTranslationSample (s : ℕ) (x : Fin 3 → ℤ) :
    Option (ReplicatedIndex (mixedCorrelationDegree s)) → ℤ
  | none => x 2
  | some j => correlationInput (x 0) (x 1) j.1

def mixedTranslationSampleHom (s : ℕ) (j : Option (ReplicatedIndex (mixedCorrelationDegree s))) :
    ((Fin 3 → ℤ) →+ ℤ) where
  toFun x := mixedTranslationSample s x j
  map_zero' := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl
  map_add' x y := by
    rcases j with _ | ⟨j, k⟩
    · rfl
    · fin_cases j <;> rfl

theorem mixedTranslationSample_translated (s : ℕ) (x : Fin 3 → ℤ) :
    coordinateTranslatedInput (mixedTranslationCoordinates s) (mixedTranslationSample s x) =
      fun j => correlationInput (x 0) (x 1 + x 2) j.1 := by
  funext ⟨j, k⟩
  fin_cases j <;> simp [coordinateTranslatedInput, mixedTranslationSample, correlationInput]
  rfl

theorem replicatedMixed_nonempty (s : ℕ) : Nonempty (ReplicatedIndex (mixedCorrelationDegree s)) :=
  ⟨⟨0, ⟨0, by change 0 < 1; omega⟩⟩⟩

theorem replicatedMixed_card (s : ℕ) :
    Fintype.card (ReplicatedIndex (mixedCorrelationDegree s)) = s + 1 := by
  rw [replicatedIndex_card, Fin.sum_univ_two]
  change 1 + s = s + 1
  omega

namespace NativeMultidegreeNilcharacter

theorem mixedTranslationExpansion_factor {s : ℕ} {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p)
    (a : BinaryTensorIndex (Fin V.outputDim) (mixedTranslationCoordinates s).length) (x : Fin 3 → ℤ) :
    coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) =
      V.eval (firstTranslationCoordinate (mixedTranslationCoordinates s) a)
        (fun j => correlationInput (x 0) (x 1) j.1) *
      translationExpansionRemainder V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x) :=
  coordinateTranslationExpansion_factor V.eval (mixedTranslationCoordinates s) a (mixedTranslationSample s x)

theorem exists_mixed_translation_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun k (x : Fin 3 → ℤ) => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1))
        (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
          (mixedTranslationSample s x)) := by
  let := replicatedMixed_nonempty s
  obtain ⟨C, hC, hexpand⟩ := exists_translation_expansion_equivalence (mixedTranslationCoordinates s)
  refine ⟨C, hC, ?_⟩
  intro p V
  have E := (hexpand V (mixedTranslationCoordinates_nodup s)).linearPullbackHom
    (mixedTranslationSampleHom s)
  change NativeIntegerVectorEquivalence _ _
    (fun k x => V.eval k (coordinateTranslatedInput (mixedTranslationCoordinates s)
      (mixedTranslationSample s x)))
    (fun a x => coordinateTranslationExpansion V.eval (mixedTranslationCoordinates s) a
      (mixedTranslationSample s x)) at E
  simpa only [replicatedMixed_card, Nat.add_sub_cancel, mixedTranslationSample_translated] using E

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_binary_assignment_equivalence {σ : Type*}
    [Fintype σ] [DecidableEq σ] [Nonempty σ] (l : List σ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p),
      l.Nodup → NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (fun j x => W.eval j (coordinateTranslatedInput l x))
        (fun a : (Fin l.length → Fin 2) → Fin W.outputDim => fun x =>
          ∏ v : Fin l.length → Fin 2, W.eval (a v) (binaryLeafInput l v x)) := by
  obtain ⟨A, _, hexpand⟩ := exists_translation_expansion_equivalence l
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C (2 ^ l.length) * X + X)
  refine ⟨C, hC, ?_⟩
  intro p W hl
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hsum : (p + A) ^ A + (2 ^ l.length : ℕ) * p + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hnp : 0 ≤ (2 ^ l.length : ℕ) * p := by positivity
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hnC : (2 ^ l.length : ℕ) * p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card ((Fin l.length → Fin 2) → Fin W.outputDim) : ℝ) ≤
      Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp p ^ (2 ^ l.length) := pow_le_pow_left₀ (Nat.cast_nonneg _) W.output_bound _
      _ = Real.exp ((2 ^ l.length : ℕ) * p) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnC
  apply (hexpand W hl).of_coordinate_maps _ _ id (binaryIndexOfFunction l.length)
    (fun _ _ => rfl) _ _ hdim hAC
  · intro a x
    exact (coordinateTranslationExpansion_leaves W.eval l a x).symm
  · simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpC)

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
