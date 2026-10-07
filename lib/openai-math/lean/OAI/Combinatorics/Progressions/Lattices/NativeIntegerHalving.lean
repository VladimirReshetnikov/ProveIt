import OAI.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
import OAI.Combinatorics.Progressions.Geometry.NativeEquivalenceCoordinateMaps

namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {σ : Type*} {w : σ → ℕ} {s d e : ℕ} {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest w) (U : E.Niltest w)
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeIntegerExpansion w s (productNiltestBudget p)
      (fun x => T.eval x * U.eval x) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest w := fun b => by
    cases b
    · exact U
    · exact T
  have htests : ∀ b, (tests b).ComplexityLE p := by
    intro b
    cases b
    · exact hU
    · exact hT
  have hcard : (Fintype.card Bool : ℝ) ≤ p := by
    simpa only [Fintype.card_bool, Nat.cast_ofNat] using hp
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis models).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis models)
  let S := RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests
  have heval (x : σ → ℤ) : S.eval x =
      T.eval x * U.eval x := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      x = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  exact ofTest S
    (RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (fun x => (heval x).symm)

noncomputable def mul {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (F : NativeIntegerExpansion w s p g)
    (hp : 2 ≤ p) :
    NativeIntegerExpansion w s (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → (σ → ℤ) → ℂ := fun ij x =>
    (E.test ij.1).eval x * (F.test ij.2).eval x
  let R : ∀ ij, NativeIntegerExpansion w s (productNiltestBudget p) (v ij) :=
    fun ij => ofProduct (E.model ij.1) (F.model ij.2) (E.test ij.1) (F.test ij.2)
      hp (E.complexity ij.1) (F.complexity ij.2)
  have hexp : Real.exp p * Real.exp p = Real.exp (2 * p) := by
    rw [← Real.exp_add, two_mul]
  have hcard : (Fintype.card (Fin E.count × Fin F.count) : ℝ) ≤ Real.exp (2 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul E.count_bound F.count_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq hexp
  have hc : (∑ ij, ‖c ij‖) ≤ Real.exp (2 * p) := by
    calc
      _ = (∑ i, ‖E.coefficient i‖) * (∑ j, ‖F.coefficient j‖) := by
        simp only [c, norm_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul E.cost F.cost (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Real.exp_nonneg _)
      _ = _ := hexp
  have heq : (fun x => ∑ ij, c ij * v ij x) = (fun x => f x * g x) := by
    funext x
    rw [E.eval x, F.eval x]
    simp only [c, v, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact heq ▸ weightedSum R c (by linarith) hcard hc

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem trans {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s : ℕ} {p : ℝ}
    {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta) (F : NativeIntegerVectorEquivalence s p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p + p) chi psi := by
  classical
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hpq : p ≤ productNiltestBudget p + 2 * p + p := by linarith
  refine {
    left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
    right_dimension := F.right_dimension.trans (Real.exp_le_exp.mpr hpq)
    expansion := ?_
  }
  intro j l
  let A : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeIntegerExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
  have heq : (fun x => ∑ k, (1 : ℂ) *
      ((chi j x * star (eta k x)) * (eta k x * star (psi l x)))) =
      (fun x => chi j x * star (psi l x)) := by
    funext x
    calc
      _ = ∑ k, ((chi j x * star (psi l x)) * star (eta k x)) * eta k x := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (complex_unit_vector_resolution (fun k => eta k x) (hunit x) _).symm
  exact ⟨heq ▸ S⟩

theorem exists_trans_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
      {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ} {psi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta → NativeIntegerVectorEquivalence s p eta psi →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence s ((p + C) ^ C) chi psi := by
  let Y : Polynomial ℕ := Polynomial.X + 2
  let P := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4 + 2 * Y + Y
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J K M _ _ _ s p chi eta psi hp E F hunit
  have hpq : p ≤ p + 2 := by linarith
  have hbudget : productNiltestBudget (p + 2) + 2 * (p + 2) + (p + 2) ≤ (p + C) ^ C := by
    simpa [P, Y, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget]
      using hbound p hp
  exact ((E.mono hpq).trans (F.mono hpq) hunit (by linarith)).mono hbudget

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

noncomputable def constOne {σ : Type*} (w : σ → ℕ) (s : ℕ) {p : ℝ} (hp : 2 ≤ p) :
    NativeIntegerExpansion w s p (fun _ => 1) :=
  ofTest (RationalFilteredNilmanifold.Niltest.const (RationalTorus.trivialNilmanifold s) w 1)
    (RationalTorus.trivialNilmanifold_const_one_complexity s w hp) (fun _ => rfl)

theorem exists_mul_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      {f g : (σ → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion w s p f → NativeIntegerExpansion w s p g →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => f x * g x)) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ w s p f g hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ⟨(((E.mono hpq).mul (F.mono hpq) (by linarith)).mono hbound)⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

theorem card_product_le_exp_two {A B : Type*} [Fintype A] [Fintype B] {p : ℝ}
    (ha : (Fintype.card A : ℝ) ≤ Real.exp p) (hb : (Fintype.card B : ℝ) ≤ Real.exp p) :
    (Fintype.card (A × B) : ℝ) ≤ Real.exp (2 * p) := by
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact (mul_le_mul ha hb (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
    (by rw [← Real.exp_add, two_mul])

theorem complex_tensor_cross_product (a b c d : ℂ) :
    (a * star b) * (c * star d) = (a * c) * star (b * d) := by
  simp only [star_mul]
  ring

noncomputable def NativeIntegerExpansion.tensorCrossProduct {σ : Type*} {s : ℕ} {p : ℝ}
    {f g h k : (σ → ℤ) → ℂ}
    (A : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => f x * star (h x)))
    (B : NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => g x * star (k x)))
    (hp : 2 ≤ p) :
    NativeIntegerExpansion (fun _ : σ => 1) s (productNiltestBudget p + 2 * p)
      (fun x => (f x * g x) * star (h x * k x)) := by
  have heq : (fun x => (f x * star (h x)) * (g x * star (k x))) =
      (fun x => (f x * g x) * star (h x * k x)) :=
    funext (fun x => complex_tensor_cross_product (f x) (h x) (g x) (k x))
  exact heq ▸ A.mul B hp

namespace NativeIntegerVectorEquivalence

theorem tensor {σ J K L M : Type*} [Fintype J] [Fintype K] [Fintype L] [Fintype M]
    {s : ℕ} {p : ℝ} {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
    {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p chi eta)
    (F : NativeIntegerVectorEquivalence s p psi phi) (hp : 2 ≤ p) :
    NativeIntegerVectorEquivalence s (productNiltestBudget p + 2 * p)
      (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
      (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  have hp0 : 0 ≤ p := by linarith
  have hB : 0 ≤ productNiltestBudget p :=
    (sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0)
  have hcost : Real.exp (2 * p) ≤ Real.exp (productNiltestBudget p + 2 * p) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hB)
  refine ⟨(card_product_le_exp_two E.left_dimension F.left_dimension).trans hcost,
    (card_product_le_exp_two E.right_dimension F.right_dimension).trans hcost, ?_⟩
  intro jl km
  obtain ⟨A⟩ := E.expansion jl.1 km.1
  obtain ⟨B⟩ := F.expansion jl.2 km.2
  exact ⟨A.tensorCrossProduct B hp⟩

theorem exists_tensor_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K L M : Type*}
      [Fintype J] [Fintype K] [Fintype L] [Fintype M] {s : ℕ} {p : ℝ}
      {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
      {psi : L → (σ → ℤ) → ℂ} {phi : M → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p chi eta →
      NativeIntegerVectorEquivalence s p psi phi →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun jl : J × L => fun x => chi jl.1 x * psi jl.2 x)
        (fun km : K × M => fun x => eta km.1 x * phi km.2 x) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + 2 + Polynomial.C a) ^ a + 2 * (X + 2))
  refine ⟨C, hC, ?_⟩
  intro σ J K L M _ _ _ _ s p chi eta psi phi hp E F
  have hpq : p ≤ p + 2 := by linarith
  have hcost : (p + 2 + a) ^ a + 2 * (p + 2) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (p + 2) + 2 * (p + 2) ≤ (p + C) ^ C :=
    (add_le_add (ha _ (by linarith)) (le_refl _)).trans hcost
  exact ((E.mono hpq).tensor (F.mono hpq) (by linarith)).mono hbound

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_fin_prod_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      (f : Fin n → (σ → ℤ) → ℂ), 0 ≤ p →
      (∀ i, Nonempty (NativeIntegerExpansion w s p (f i))) →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => ∏ i, f i x)) := by
  induction n with
  | zero =>
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Polynomial.X + 2)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp _
    have hcost : p + 2 ≤ (p + C) ^ C := by simpa using hbudget p hp
    exact ⟨by simpa using (constOne w s (by linarith : 2 ≤ p + 2)).mono hcost⟩
  | succ n ih =>
    obtain ⟨A, _, hprod⟩ := ih
    obtain ⟨B, _, hmul⟩ := exists_mul_budget
    let X : Polynomial ℕ := Polynomial.X
    let T := X + (X + Polynomial.C A) ^ A
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B)
    refine ⟨C, hC, ?_⟩
    intro σ w s p f hp hf
    let t := p + (p + A) ^ A
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
    have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
    obtain ⟨tail⟩ := hprod (fun i => f i.succ) hp (fun i => hf i.succ)
    obtain ⟨H⟩ := hmul ht ((Classical.choice (hf 0)).mono hpt) (tail.mono hAt)
    have hcost : (t + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
    exact ⟨by simpa only [Fin.prod_univ_succ] using H.mono hcost⟩

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_cancel_left_tensor_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J K L : Type*}
      [Fintype I] [Fintype J] [Fintype K] [Fintype L] {s : ℕ} {p : ℝ}
      {a : I → (σ → ℤ) → ℂ} {b : J → (σ → ℤ) → ℂ}
      {c : K → (σ → ℤ) → ℂ} {d : L → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p a b →
      NativeIntegerVectorEquivalence s p c (fun jl : J × L => fun x => b jl.1 x * d jl.2 x) →
      (∀ x, ∑ j, ‖b j x‖ ^ 2 = 1) → (Fintype.card L : ℝ) ≤ Real.exp p →
      NativeIntegerVectorEquivalence s ((p + C) ^ C)
        (fun ik : I × K => fun x => a ik.1 x * star (c ik.2 x)) (fun l x => star (d l x)) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + 3 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro σ I J K L _ _ _ _ s p a b c d hp E F hunit hdim
  have hcost : (p + A) ^ A + 3 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have htwo : 2 * p ≤ (p + C) ^ C := by linarith
  have hsumCost : (p + A) ^ A + p ≤ (p + C) ^ C := by linarith
  refine ⟨(card_product_le_exp_two E.left_dimension F.left_dimension).trans
    (Real.exp_le_exp.mpr htwo), hdim.trans (Real.exp_le_exp.mpr hpC), ?_⟩
  intro ik l
  let term (j : J) (x : σ → ℤ) :=
    (a ik.1 x * star (b j x)) * star (c ik.2 x * star (b j x * d l x))
  have hterm (j : J) : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + A) ^ A) (term j)) :=
    hmul hp (Classical.choice (E.expansion ik.1 j)) (Classical.choice (F.expansion ik.2 (j, l))).conjugate
  have hcoeff : (∑ _j : J, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using E.right_dimension
  have S := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hterm j))
    (fun _ => (1 : ℂ)) hp E.right_dimension hcoeff).mono hsumCost
  have heq : (fun x => ∑ j : J, (1 : ℂ) * term j x) =
      (fun x => (a ik.1 x * star (c ik.2 x)) * star (star (d l x))) := by
    funext x
    simp only [one_mul, star_star]
    calc
      _ = (∑ j : J, (a ik.1 x * star (b j x)) * b j x) * (star (c ik.2 x) * d l x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        simp only [term, star_mul, star_star]
        ring
      _ = _ := by
        rw [← complex_unit_vector_resolution (fun j => b j x) (hunit x) (a ik.1 x)]
        ring
  exact ⟨heq ▸ S⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem RationalTorus.residueNiltest_eval {q : ℕ} [NeZero q] (j : ZMod q) (n : ℤ) :
    (residueNiltest j).eval (fun _ : Unit => n) = if (n : ZMod q) = j then 1 else 0 := by
  classical
  unfold residueNiltest realAffineNiltest
  rw [affineNiltest_eval]
  simp only [reindexedRealObservable, Equiv.refl_apply,
    Finset.univ_unique, Finset.sum_singleton, Pi.add_apply, Pi.smul_apply,
    zero_add, smul_eq_mul, mul_one_div]
  rw [← ZMod.toAddCircle_intCast, CircleFourier.residueCutoff_at_grid]
  split_ifs <;> rfl

theorem exists_coordinate_residue_expansion {σ : Type*} [Fintype σ]
    {q : ℕ} [NeZero q] (k : σ) (j : ZMod q) {p : ℝ}
    (hp : 0 ≤ p) (hq : (q : ℝ) ≤ Real.exp p) :
    Nonempty (NativeIntegerExpansion (fun _ : σ => 1) 1 (p + 2)
      (fun x => if (x k : ZMod q) = j then 1 else 0)) := by
  let T := RationalTorus.residueNiltest j
  let a : (σ → ℤ) →+ ℤ := { toFun := fun x => x k, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom (fun _ : Unit => a)
  refine ⟨NativeIntegerExpansion.ofTest U (RationalTorus.residueNiltest_complexity j hp hq) ?_⟩
  intro x
  rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
  exact (RationalTorus.residueNiltest_eval j (x k)).symm

noncomputable def pairParityIndicator (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) : ℂ :=
  if (fun i => (x i : ZMod 2)) = r then 1 else 0

theorem pairParityIndicator_product (r : Fin 2 → ZMod 2) (x : Fin 2 → ℤ) :
    pairParityIndicator r x =
      (if (x 0 : ZMod 2) = r 0 then 1 else 0) *
        (if (x 1 : ZMod 2) = r 1 then 1 else 0) := by
  classical
  have heq : (fun i => (x i : ZMod 2)) = r ↔ (x 0 : ZMod 2) = r 0 ∧ (x 1 : ZMod 2) = r 1 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨h0, h1⟩
      funext i
      fin_cases i <;> assumption
  unfold pairParityIndicator
  simp only [heq]
  split_ifs <;> simp_all

theorem exists_pairParityIndicator_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ r : Fin 2 → ZMod 2,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 (C : ℝ) (pairParityIndicator r)) := by
  obtain ⟨A, hA, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨(4 + A) ^ A + 2, by omega, ?_⟩
  intro r
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  obtain ⟨E0⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 0 (r 0) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E1⟩ := exists_coordinate_residue_expansion (σ := Fin 2) 1 (r 1) (by norm_num : (0 : ℝ) ≤ 2) htwo
  obtain ⟨E⟩ := hmul (by norm_num : (0 : ℝ) ≤ 2 + 2) E0 E1
  have hb : ((2 : ℝ) + 2 + A) ^ A ≤ (((4 + A) ^ A + 2 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have heq : (fun x => (if (x 0 : ZMod 2) = r 0 then (1 : ℂ) else 0) *
      (if (x 1 : ZMod 2) = r 1 then 1 else 0)) = pairParityIndicator r := by
    funext x
    exact (pairParityIndicator_product r x).symm
  rw [heq] at E
  exact ⟨E.mono hb⟩

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem exists_tensor_power_budget (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
      {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ},
      0 ≤ p → NativeIntegerVectorEquivalence s p f g →
      NativeIntegerVectorEquivalence s ((p + C) ^ C) (tensorVector f n) (tensorVector g n) := by
  obtain ⟨A, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget n
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C n * X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s p f g hp E
  have hsum : (p + A) ^ A + n * p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + A) ^ A ≤ (p + C) ^ C := by
    have hn : 0 ≤ (n : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
    linarith
  have hnp : (n : ℝ) * p ≤ (p + C) ^ C := by
    have ha : 0 ≤ (p + A) ^ A := by positivity
    linarith
  have hI : (Fintype.card (Fin n → I) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.left_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  have hJ : (Fintype.card (Fin n → J) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp p) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg _) E.right_dimension n
      _ = Real.exp ((n : ℝ) * p) := (Real.exp_nat_mul p n).symm
      _ ≤ _ := Real.exp_le_exp.mpr hnp
  refine ⟨hI, hJ, ?_⟩
  intro a b
  obtain ⟨F⟩ := hprod (fun k x => f (a k) x * star (g (b k) x)) hp
    (fun k => E.expansion (a k) (b k))
  have heq : (fun x => ∏ k, f (a k) x * star (g (b k) x)) =
      (fun x => tensorVector f n a x * star (tensorVector g n b x)) := by
    funext x
    simp only [tensorVector, Finset.prod_mul_distrib, star_prod]
  exact ⟨heq ▸ F.mono hcost⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

theorem exists_halving_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} {f : (Fin 2 → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 p f →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (fun x => f (fun i => x i / 2))) := by
  obtain ⟨A, hA, hparity⟩ := exists_pairParityIndicator_expansion
  obtain ⟨B, _, hmul⟩ := exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A + 2 + Polynomial.C B) ^ B + 2)
  refine ⟨C, hC, ?_⟩
  intro p f hp E
  classical
  let t : ℝ := p + A + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hAt : (A : ℝ) ≤ t := by dsimp [t]; linarith
  let P (r : Fin 2 → ZMod 2) := halvingPolynomial (fun i => ((r i).val : ℤ))
  have hP (r : Fin 2 → ZMod 2) (i : Fin 2) :
      P r i ∈ weightedSupportLE (fun _ : Fin 2 => 1) 1 := halvingPolynomial_support _ i
  let F (r : Fin 2 → ZMod 2) := E.substitutedValue (P r) (hP r)
  have hF (r : Fin 2 → ZMod 2) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
      ((t + B) ^ B) (fun x => pairParityIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hparity r)).mono hAt)
      ((E.substituteExpansion (P r) (hP r)).mono hpt)
  have hc : (Fintype.card (Fin 2 → ZMod 2) : ℝ) ≤ Real.exp 2 := by
    norm_num only [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hh := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hcost : (∑ _ : Fin 2 → ZMod 2, ‖(1 : ℂ)‖) ≤ Real.exp 2 := by simpa using hc
  let S := weightedSum (fun r => Classical.choice (hF r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 2) hc hcost
  have heq : (fun x => ∑ r : Fin 2 → ZMod 2, (1 : ℂ) * (pairParityIndicator r x * F r x)) =
      (fun x => f (fun i => x i / 2)) := by
    funext x
    let r : Fin 2 → ZMod 2 := fun i => (x i : ZMod 2)
    rw [Finset.sum_eq_single r]
    · simp only [pairParityIndicator, r, ite_true, one_mul]
      apply E.substitutedValue_eq (P r) (hP r) x (fun i => x i / 2)
      exact halvingPolynomial_eval _ x (fun i => (ZMod.val_intCast (x i)).symm)
    · intro a _ ha
      have hne : (fun i => (x i : ZMod 2)) ≠ a := fun h => ha h.symm
      simp only [pairParityIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  have hb : (t + B) ^ B + 2 ≤ (p + C) ^ C := by
    simpa [t, X, Polynomial.eval₂_pow] using hbudget p hp
  rw [heq] at S
  exact ⟨S.mono hb⟩

end Erdos3.NativeIntegerExpansion

end

end OAI
