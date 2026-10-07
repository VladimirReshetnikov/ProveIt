import OAI.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
import OAI.Combinatorics.Progressions.Nilpotent.NativeNilsequenceExpansion

namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def BoolLieFamily (L₁ L₂ : Type u) : Bool → Type u
  | false => L₂
  | true => L₁

namespace BoolLieFamily

variable {L₁ L₂ : Type u} [LieRing L₁] [LieAlgebra ℚ L₁]
    [LieRing L₂] [LieAlgebra ℚ L₂]

instance instLieRing (b : Bool) : LieRing (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieRing L₂)
  · exact (inferInstance : LieRing L₁)

instance instLieAlgebra (b : Bool) : LieAlgebra ℚ (BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : LieAlgebra ℚ L₂)
  · exact (inferInstance : LieAlgebra ℚ L₁)

variable [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
    [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)]

instance instTopologicalSpace (b : Bool) :
    TopologicalSpace (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L₁))

instance instIsTopologicalAddGroup (b : Bool) :
    IsTopologicalAddGroup (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁))

instance instContinuousSMul (b : Bool) :
    ContinuousSMul ℝ (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁))

instance instT2Space (b : Bool) : T2Space (ℝ ⊗[ℚ] BoolLieFamily L₁ L₂ b) := by
  cases b
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₂))
  · exact (inferInstance : T2Space (ℝ ⊗[ℚ] L₁))

end BoolLieFamily
end Erdos3

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s N : ℕ} [NeZero N] {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : I → ℂ)
    {p : ℝ} {f : ZMod N → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).evalCyclic N (fun _ => x)) :
    NativeNilsequenceExpansion s N p f := by
  let e := (Fintype.equivFin I).symm
  exact {
    count := Fintype.card I
    count_bound := hcard
    L := fun i => L (e i)
    dim := fun i => d (e i)
    model := fun i => D (e i)
    test := fun i => T (e i)
    complexity := fun i => hT (e i)
    coefficient := fun i => c (e i)
    cost := (e.sum_comp (fun i => ‖c i‖)).le.trans hc
    eval := fun x => (hf x).trans (e.sum_comp
      (fun i => c i * (T i).evalCyclic N (fun _ => x))).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {s N : ℕ} [NeZero N]
    {p q : ℝ} {f : I → ZMod N → ℂ} (E : ∀ i, NativeNilsequenceExpansion s N p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeNilsequenceExpansion s N (p + q) (fun x => ∑ i, c i * f i x) := by
  classical
  let A := Σ i, Fin (E i).count
  refine ofFamily (I := A) (fun a => (E a.1).model a.2)
    (fun a => (E a.1).test a.2) (fun a => c a.1 * (E a.1).coefficient a.2) ?_
    (fun a => ((E a.1).complexity a.2).mono (by linarith)) ?_ ?_
  · change (Fintype.card (Σ i, Fin (E i).count) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _ : I, Real.exp p := Finset.sum_le_sum (fun i _ => by
        simpa only [Fintype.card_fin] using (E i).count_bound)
      _ = (Fintype.card I : ℝ) * Real.exp p := by simp
      _ ≤ Real.exp q * Real.exp p := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p + q) := by rw [← Real.exp_add, add_comm]
  · exact (sum_pair_coefficient_norms_le c (fun i => (E i).coefficient)
      (Real.exp_nonneg p) hc (fun i => (E i).cost)).trans_eq
      (by rw [← Real.exp_add, add_comm])
  · intro x
    change (∑ i, c i * f i x) = ∑ a : Sigma (fun i => Fin (E i).count), _
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    rw [(E i).eval x, Finset.mul_sum]
    simp only [mul_assoc]

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

variable {J K : Type*} [Fintype J] [Fintype K] {s N : ℕ} [NeZero N] {p q : ℝ}
  {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}

theorem mono (E : NativeVectorEquivalence s N p chi chi') (hpq : p ≤ q) :
    NativeVectorEquivalence s N q chi chi' where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

theorem symm (E : NativeVectorEquivalence s N p chi chi') :
    NativeVectorEquivalence s N p chi' chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeNilsequenceExpansion s N p
        (fun x => star (chi j x * star (chi' k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem conjugate (E : NativeVectorEquivalence s N p chi chi') :
    NativeVectorEquivalence s N p (fun j x => star (chi j x)) (fun k x => star (chi' k x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeNilsequenceExpansion s N p
        (fun x => star (chi j x * star (chi' k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff

noncomputable def ofProduct {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    {s d e N : ℕ} [NeZero N] {p : ℝ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
    (T : D.Niltest (fun _ : Unit => 1)) (U : E.Niltest (fun _ : Unit => 1))
    (hp : 2 ≤ p) (hT : T.ComplexityLE p) (hU : U.ComplexityLE p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p)
      (fun x => T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x)) := by
  have hp0 : 0 ≤ p := by linarith
  let K : Bool → Type := BoolLieFamily L M
  let dims : Bool → ℕ := fun b => Bool.rec e d b
  let models : ∀ b, RationalFilteredNilmanifold (K b) s (dims b) := fun b => by
    cases b
    · exact E
    · exact D
  let tests : ∀ b, (models b).Niltest (fun _ : Unit => 1) := fun b => by
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
  have heval (x : ZMod N) : S.evalCyclic N (fun _ => x) =
      T.evalCyclic N (fun _ => x) * U.evalCyclic N (fun _ => x) := by
    change (RationalFilteredNilmanifold.piNiltest models tests hp0 hcard htests).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    rfl
  have hB : 1 ≤ Real.exp (productNiltestBudget p) :=
    Real.one_le_exp_iff.mpr ((sq_nonneg (p + 2)).trans (productNiltestBudget_geometry hp0))
  refine ofFamily (I := Unit) (fun _ => RationalFilteredNilmanifold.pi models)
    (fun _ => S) (fun _ => 1) (by simpa using hB)
    (fun _ => RationalFilteredNilmanifold.piNiltest_complexity models tests hp0 hcard htests)
    (by simpa using hB) ?_
  intro x
  simpa only [one_mul, Fintype.sum_unique] using (heval x).symm

noncomputable def mul {s N : ℕ} [NeZero N] {p : ℝ} {f g : ZMod N → ℂ}
    (E : NativeNilsequenceExpansion s N p f) (F : NativeNilsequenceExpansion s N p g)
    (hp : 2 ≤ p) :
    NativeNilsequenceExpansion s N (productNiltestBudget p + 2 * p) (fun x => f x * g x) := by
  let c : Fin E.count × Fin F.count → ℂ := fun ij => E.coefficient ij.1 * F.coefficient ij.2
  let v : Fin E.count × Fin F.count → ZMod N → ℂ := fun ij x =>
    (E.test ij.1).evalCyclic N (fun _ => x) * (F.test ij.2).evalCyclic N (fun _ => x)
  let R : ∀ ij, NativeNilsequenceExpansion s N (productNiltestBudget p) (v ij) :=
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

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped BigOperators

theorem trans {J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
    {s N : ℕ} [NeZero N] {p : ℝ}
    {chi : J → ZMod N → ℂ} {eta : K → ZMod N → ℂ} {psi : M → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi eta) (F : NativeVectorEquivalence s N p eta psi)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) (hp : 2 ≤ p) :
    NativeVectorEquivalence s N (productNiltestBudget p + 2 * p + p) chi psi := by
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
  let A : ∀ k, NativeNilsequenceExpansion s N p (fun x => chi j x * star (eta k x)) :=
    fun k => Classical.choice (E.expansion j k)
  let B : ∀ k, NativeNilsequenceExpansion s N p (fun x => eta k x * star (psi l x)) :=
    fun k => Classical.choice (F.expansion k l)
  let R := fun k => (A k).mul (B k) hp
  have hc : (∑ _ : K, ‖(1 : ℂ)‖) ≤ Real.exp p := by
    simpa only [norm_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      using E.right_dimension
  let S := NativeNilsequenceExpansion.weightedSum R (fun _ => 1) hp0 E.right_dimension hc
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
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J K M : Type*} [Fintype J] [Fintype K] [Fintype M]
      {s N : ℕ} [NeZero N] {p : ℝ}
      {chi : J → ZMod N → ℂ} {eta : K → ZMod N → ℂ} {psi : M → ZMod N → ℂ},
      0 ≤ p → NativeVectorEquivalence s N p chi eta → NativeVectorEquivalence s N p eta psi →
      (∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) → NativeVectorEquivalence s N ((p + C) ^ C) chi psi := by
  let Y : Polynomial ℕ := Polynomial.X + 2
  let P := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4 + 2 * Y + Y
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro J K M _ _ _ s N _ p chi eta psi hp E F hunit
  have hpq : p ≤ p + 2 := by linarith
  have hbudget : productNiltestBudget (p + 2) + 2 * (p + 2) + (p + 2) ≤ (p + C) ^ C := by
    simpa [P, Y, Polynomial.eval₂_pow, productNiltestBudget, productObservableLipBudget]
      using hbound p hp
  exact ((E.mono hpq).trans (F.mono hpq) hunit (by linarith)).mono hbudget

end Erdos3.NativeVectorEquivalence

end

end OAI
