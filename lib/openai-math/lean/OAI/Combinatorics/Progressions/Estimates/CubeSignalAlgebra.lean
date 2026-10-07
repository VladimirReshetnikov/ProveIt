/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.MultidegreeIntegerTranslation
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerEquivalenceFiniteFamily

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInput {d : ℕ} (ω : Fin d → Bool) (x : Fin (d + 2) → ℤ) : Fin 2 → ℤ :=
  correlationInput (x 0) (x 1 + cubeShift (fun j => x j.succ.succ) ω)

namespace NativeMultidegreeNilcharacter

noncomputable def mixedCubeWithShift {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (a : (Fin d → Bool) → Fin M.outputDim)
    (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω)
    (M.eval (a ω) (mixedCubeInput ω x + ![0, c ω]))

theorem mixedCubeWithShift_unit {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (x : Fin (d + 2) → ℤ) :
    ∑ a, ‖M.mixedCubeWithShift c a x‖ ^ 2 = 1 := by
  simp only [mixedCubeWithShift, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (i : Fin M.outputDim) =>
    ‖M.eval i (mixedCubeInput ω x + ![0, c ω])‖ ^ 2)]
  simp only [M.unit_eval, Finset.prod_const_one]

theorem mixedCubeWithShift_diagonal {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (c : (Fin d → Bool) → ℤ) (i : Fin M.outputDim) (h n : ℤ) (k : Fin d → ℤ) :
    M.mixedCubeWithShift c (fun _ => i) (Fin.cons h (Fin.cons n k)) =
      integerCubeProductWithShift (fun z => M.eval i (correlationInput h z)) k c n := by
  have hinput (ω : Fin d → Bool) :
      mixedCubeInput ω (Fin.cons h (Fin.cons n k)) + ![0, c ω] =
        correlationInput h (n + cubeShift k ω + c ω) := by
    funext j
    fin_cases j <;> simp [mixedCubeInput, correlationInput, cubeShift]
    rfl
  simp only [mixedCubeWithShift, integerCubeProductWithShift, hinput]

theorem exists_mixed_cube_translation (s d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
      (c : (Fin d → Bool) → ℤ),
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (M.mixedCubeWithShift c) (M.mixedCubeWithShift 0) := by
  obtain ⟨A, _, htranslate⟩ := exists_multidegree_integer_translation s
  obtain ⟨B, _, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := X + P
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p M c
  have hp : 0 ≤ p := (Nat.cast_nonneg M.dim).trans M.complexity.1.1
  let q := (p + A) ^ A
  let u := p + q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := add_nonneg hp hq
  have hpu : p ≤ u := le_add_of_nonneg_right hq
  have hqu : q ≤ u := le_add_of_nonneg_left hp
  have hcost : (u + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hdegree : (∑ i, mixedCorrelationDegree s i) = s + 1 := by
    rw [Fin.sum_univ_two]
    change 1 + s = s + 1
    omega
  let F (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) := fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  have E (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, 0])) := by
    have T := ((htranslate (mixedCorrelationDegree s) hdegree M ![0, c ω] 0).linearPullbackHom (F ω)).mono hqu
    change NativeIntegerVectorEquivalence s u
      (fun i x => M.eval i (mixedCubeInput ω x + ![0, c ω]))
      (fun i x => M.eval i (mixedCubeInput ω x + 0)) at T
    simpa only [hzero] using T
  have hdim : (Fintype.card (Fin M.outputDim) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin] using M.output_bound.trans (Real.exp_le_exp.mpr hpu)
  exact (hprod _ _ hu hdim hdim (fun ω => (E ω).conjugationPower (booleanWeight ω))).mono hcost

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedCubeInputHom {d : ℕ} (ω : Fin d → Bool) : Fin 2 → ((Fin (d + 2) → ℤ) →+ ℤ) :=
  fun i =>
    { toFun := fun x => mixedCubeInput ω x i
      map_zero' := by
        fin_cases i <;> simp [mixedCubeInput, correlationInput, cubeShift]
        rfl
      map_add' := by
        intro x y
        fin_cases i
        · rfl
        · change x 1 + y 1 + cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
            (x 1 + cubeShift (fun j => x j.succ.succ) ω) +
              (y 1 + cubeShift (fun j => y j.succ.succ) ω)
          have hs : cubeShift (fun j => x j.succ.succ + y j.succ.succ) ω =
              cubeShift (fun j => x j.succ.succ) ω + cubeShift (fun j => y j.succ.succ) ω := by
            simp only [cubeShift, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            split_ifs <;> simp
          rw [hs]
          ring }

def mixedCubeObservable {J : Type*} {d : ℕ} (f : J → (Fin 2 → ℤ) → ℂ)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (f (a ω) (mixedCubeInput ω x))

theorem mixedCubeObservable_unit {J : Type*} [Fintype J] {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ y, ∑ j, ‖f j y‖ ^ 2 = 1)
    (x : Fin (d + 2) → ℤ) : ∑ a, ‖mixedCubeObservable f a x‖ ^ 2 = 1 := by
  simp only [mixedCubeObservable, norm_prod, ← Finset.prod_pow, conjugationPower_norm]
  rw [← Fintype.prod_sum (fun ω (j : J) => ‖f j (mixedCubeInput ω x)‖ ^ 2)]
  simp only [hf, Finset.prod_const_one]

theorem NativeMultidegreeNilcharacter.mixedCubeWithShift_zero_eq {s d : ℕ} {p : ℝ}
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p) :
    M.mixedCubeWithShift (d := d) 0 = mixedCubeObservable M.eval := by
  funext a x
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  simp only [NativeMultidegreeNilcharacter.mixedCubeWithShift, mixedCubeObservable,
    Pi.zero_apply, hzero, add_zero]

theorem NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (Fin 2 → ℤ) → ℂ} {g : J → (Fin 2 → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (mixedCubeObservable (d := d) f) (mixedCubeObservable (d := d) g) := by
  obtain ⟨C, hC, hprod⟩ := NativeIntegerVectorEquivalence.exists_finite_product_budget (Fin d → Bool)
  refine ⟨C, hC, ?_⟩
  intro I J _ _ s p f g hp E
  have H (ω : Fin d → Bool) : NativeIntegerVectorEquivalence s p
      (fun i x => f i (mixedCubeInput ω x)) (fun j x => g j (mixedCubeInput ω x)) :=
    E.linearPullbackHom (mixedCubeInputHom ω)
  exact hprod _ _ hp E.left_dimension E.right_dimension
    (fun ω => (H ω).conjugationPower (booleanWeight ω))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mixedCubeObservable_norm_le_one {J : Type*} {d : ℕ}
    (f : J → (Fin 2 → ℤ) → ℂ) (hf : ∀ j x, ‖f j x‖ ≤ 1)
    (a : (Fin d → Bool) → J) (x : Fin (d + 2) → ℤ) : ‖mixedCubeObservable f a x‖ ≤ 1 := by
  unfold mixedCubeObservable
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro ω _
  rw [conjugationPower_norm]
  exact hf _ _

theorem conjugationPower_next_self (n : ℕ) (z : ℂ) :
    conjugationPower (n + 1) (conjugationPower n z) = star z := by
  have hn : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hn with hn | hn <;> simp [conjugationPower_eq_if_mod, Nat.add_mod, hn]

theorem norm_expect_conjugationPower {X : Type*} (S : Finset X) (n : ℕ) (f : X → ℂ) :
    ‖𝔼 x ∈ S, conjugationPower n (f x)‖ = ‖𝔼 x ∈ S, f x‖ := by
  by_cases hn : n % 2 = 0
  · simp only [conjugationPower_eq_if_mod, hn, ite_true]
  · simp only [conjugationPower_eq_if_mod, hn, ite_false]
    have hs : (𝔼 x ∈ S, star (f x)) = star (𝔼 x ∈ S, f x) := by
      simp [Finset.expect_eq_sum_div_card]
    rw [hs, norm_star]

theorem cubeProduct_swap_head {G : Type*} [AddCommGroup G]
    (f : G → ℂ) (h k : G) (hs : List G) (x : G) :
    cubeProduct f (h :: k :: hs) x = cubeProduct f (k :: h :: hs) x := by
  simp only [cubeProduct_cons_eq_derivative, multiplicativeDerivative_comm f h k]

theorem cubeProduct_comp_addHom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (f : H → ℂ) (hs : List G) (x : G) :
    cubeProduct (fun y => f (φ y)) hs x = cubeProduct f (hs.map φ) (φ x) := by
  induction hs generalizing x with
  | nil => simp only [cubeProduct_nil, List.map_nil]
  | cons h hs ih => simp only [List.map_cons, cubeProduct_cons, ih, map_add]

end Erdos3

end

end OAI
