import OAI.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity
import OAI.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

structure NativeIntegerModelFamily {σ I : Type*} (w : σ → ℕ)
    (degree : ℕ) (p : ℝ) (f : I → (σ → ℤ) → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : I → model.Niltest w
  norm : ∀ i, (test i).normBound ≤ 1
  complexity : ∀ i, (test i).ComplexityLE p
  normalized : ∀ i, model.filtration.realification.polynomialOrbitEval w 0 (test i).orbit = 1
  eval : ∀ i x, (test i).eval x = f i x

attribute [local instance] NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerModelFamily

variable {σ I : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : I → (σ → ℤ) → ℂ}

noncomputable def mono (R : NativeIntegerModelFamily w s p f) (hpq : p ≤ q) :
    NativeIntegerModelFamily w s q f :=
  { R with complexity := fun i => (R.complexity i).mono hpq }

@[simp] theorem mono_dim (R : NativeIntegerModelFamily w s p f) (hpq : p ≤ q) :
    (R.mono hpq).dim = R.dim := rfl

end NativeIntegerModelFamily

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeIntegerExpansion {σ : Type*} (w : σ → ℕ)
    (s : ℕ) (p : ℝ) (f : (σ → ℤ) → ℂ) where
  count : ℕ
  count_bound : (count : ℝ) ≤ Real.exp p
  L : Fin count → Type
  [lie : ∀ i, LieRing (L i)]
  [algebra : ∀ i, LieAlgebra ℚ (L i)]
  dim : Fin count → ℕ
  [topology : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)]
  [topologicalAdd : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [continuousSMul : ∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)]
  [hausdorff : ∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  model : ∀ i, RationalFilteredNilmanifold (L i) s (dim i)
  test : ∀ i, (model i).Niltest w
  complexity : ∀ i, (test i).ComplexityLE p
  coefficient : Fin count → ℂ
  cost : (∑ i, ‖coefficient i‖) ≤ Real.exp p
  eval : ∀ x, f x = ∑ i, coefficient i * (test i).eval x

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeIntegerModelFamily.lie NativeIntegerModelFamily.algebra
  NativeIntegerModelFamily.topology NativeIntegerModelFamily.topologicalAdd
  NativeIntegerModelFamily.continuousSMul NativeIntegerModelFamily.hausdorff

namespace NativeIntegerExpansion

variable {σ : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ} {f : (σ → ℤ) → ℂ}

noncomputable def mono (E : NativeIntegerExpansion w s p f) (hpq : p ≤ q) :
    NativeIntegerExpansion w s q f :=
  { E with
    count_bound := E.count_bound.trans (Real.exp_le_exp.mpr hpq)
    complexity := fun i => (E.complexity i).mono hpq
    cost := E.cost.trans (Real.exp_le_exp.mpr hpq) }

noncomputable def conjugate (E : NativeIntegerExpansion w s p f) :
    NativeIntegerExpansion w s p (fun x => star (f x)) :=
  { E with
    test := fun i => (E.test i).conjugate
    complexity := E.complexity
    coefficient := fun i => star (E.coefficient i)
    cost := by simpa only [norm_star] using E.cost
    eval := by
      intro x
      have h := congrArg star (E.eval x)
      simpa only [star_sum, star_mul, mul_comm,
        RationalFilteredNilmanifold.Niltest.eval_conjugate] using h }

noncomputable def ofTest {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest w) (hT : T.ComplexityLE p) (hf : ∀ x, f x = T.eval x) :
    NativeIntegerExpansion w s p f := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  exact {
    count := 1
    count_bound := by simpa only [Nat.cast_one] using Real.one_le_exp hp
    L := fun _ => L
    dim := fun _ => d
    model := fun _ => D
    test := fun _ => T
    complexity := fun _ => hT
    coefficient := fun _ => 1
    cost := by simpa using Real.one_le_exp hp
    eval := fun x => by simpa using hf x }

noncomputable def ofModelFamily {I : Type*} {g : I → (σ → ℤ) → ℂ}
    (R : NativeIntegerModelFamily w s p g) (i : I) :
    NativeIntegerExpansion w s p (g i) :=
  ofTest (R.test i) (R.complexity i) (fun x => (R.eval i x).symm)

end NativeIntegerExpansion

end Erdos3

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_sample_correlation {σ X : Type*} {w : σ → ℕ} {s : ℕ} {p q : ℝ}
    {eta : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p eta)
    (S : Finset X) (sample : X → σ → ℤ) (f : X → ℂ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (eta (sample u))‖) :
    ∃ i : Fin E.count, Real.exp (-(q + p)) ≤
      ‖𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))‖ := by
  have hpoint (u : X) : f u * star (eta (sample u)) =
      ∑ i, star (E.coefficient i) * (f u * star ((E.test i).eval (sample u))) := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [star_mul]
    ring
  have hmean : (𝔼 u ∈ S, f u * star (eta (sample u))) =
      ∑ i, star (E.coefficient i) * (𝔼 u ∈ S, f u * star ((E.test i).eval (sample u))) := by
    calc
      _ = 𝔼 u ∈ S, ∑ i, star (E.coefficient i) *
          (f u * star ((E.test i).eval (sample u))) := Finset.expect_congr rfl (fun u _ => hpoint u)
      _ = _ := by simp_rw [Finset.expect_sum_comm, ← Finset.mul_expect]
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun i => star (E.coefficient i))
    (fun i => 𝔼 u ∈ S, f u * star ((E.test i).eval (sample u)))
    (Real.exp_pos (-q)) (Real.exp_pos p) (by simpa only [norm_star] using E.cost)
    (by rwa [← hmean])
  refine ⟨i, ?_⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem norm_eval_le {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ} {f : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p f) (x : σ → ℤ) : ‖f x‖ ≤ Real.exp (2 * p) := by
  rw [E.eval x]
  calc
    ‖∑ i, E.coefficient i * (E.test i).eval x‖ ≤
        ∑ i, ‖E.coefficient i * (E.test i).eval x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖E.coefficient i‖ * Real.exp p := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((E.test i).eval_budget (E.complexity i) x) (norm_nonneg _)
    _ = (∑ i, ‖E.coefficient i‖) * Real.exp p := (Finset.sum_mul _ _ _).symm
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.cost (Real.exp_nonneg _)
    _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def ofFamily {I : Type*} [Fintype I] {L : I → Type}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {σ : Type*} {w : σ → ℕ} {s : ℕ} {d : I → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (T : ∀ i, (D i).Niltest w) (c : I → ℂ)
    {p : ℝ} {f : (σ → ℤ) → ℂ} (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hT : ∀ i, (T i).ComplexityLE p) (hc : (∑ i, ‖c i‖) ≤ Real.exp p)
    (hf : ∀ x, f x = ∑ i, c i * (T i).eval x) :
    NativeIntegerExpansion w s p f := by
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
      (fun i => c i * (T i).eval x)).symm
  }

noncomputable def weightedSum {I : Type*} [Fintype I] {σ : Type*} {w : σ → ℕ} {s : ℕ}
    {p q : ℝ} {f : I → (σ → ℤ) → ℂ} (E : ∀ i, NativeIntegerExpansion w s p (f i))
    (c : I → ℂ) (hq : 0 ≤ q) (hcard : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hc : (∑ i, ‖c i‖) ≤ Real.exp q) :
    NativeIntegerExpansion w s (p + q) (fun x => ∑ i, c i * f i x) := by
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

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def affinePullback {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (integerAffineMap A b x)) :=
  { E with
    test := fun i => (E.test i).affinePullback A b
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_affinePullback] using
        E.eval (integerAffineMap A b x) }

noncomputable def toCyclic {s : ℕ} {p : ℝ} {f : (Unit → ℤ) → ℂ}
    (E : NativeIntegerExpansion (fun _ : Unit => 1) s p f) (N : ℕ) [NeZero N] :
    NativeNilsequenceExpansion s N p (fun x => f (fun _ => (x.val : ℤ))) where
  count := E.count
  count_bound := E.count_bound
  L := E.L
  dim := E.dim
  model := E.model
  test := E.test
  complexity := E.complexity
  coefficient := E.coefficient
  cost := E.cost
  eval x := E.eval (fun _ => (x.val : ℤ))

noncomputable def cyclicAffinePullback {σ : Type*} {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → Unit → ℤ) (b : σ → ℤ) (N : ℕ) [NeZero N] :
    NativeNilsequenceExpansion s N p
      (fun x => f (integerAffineMap A b (fun _ => (x.val : ℤ)))) :=
  (E.affinePullback A b).toCyclic N

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def scaleNormLeOne {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p f)
    (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeIntegerExpansion w s p (fun x => c * f x) :=
  { E with
    coefficient := fun i => c * E.coefficient i
    cost := by
      simp only [norm_mul, ← Finset.mul_sum]
      exact (mul_le_of_le_one_left (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hc).trans E.cost
    eval := by
      intro x
      rw [E.eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc _ _ _).symm }

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ τ : Type*} {w : σ → ℕ} {v : τ → ℕ} {s : ℕ} {p : ℝ}
  {f : (σ → ℤ) → ℂ}

noncomputable def substitutedValue (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) : ℂ :=
  ∑ i, E.coefficient i * ((E.test i).substitute P hP).eval x

noncomputable def substituteExpansion (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i)) :
    NativeIntegerExpansion v s p (E.substitutedValue P hP) :=
  { E with
    test := fun i => (E.test i).substitute P hP
    complexity := E.complexity
    eval := fun _ => rfl }

theorem substitutedValue_eq (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (P i) = (y i : ℚ)) :
    E.substitutedValue P hP x = f y := by
  rw [E.eval y]
  unfold substitutedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [RationalFilteredNilmanifold.Niltest.eval_substitute _ _ _ x y hxy]

end Erdos3.NativeIntegerExpansion

namespace Erdos3

noncomputable def halvingPolynomial {σ : Type*} (r : σ → ℤ) (i : σ) : MvPolynomial σ ℚ :=
  MvPolynomial.C (1 / 2 : ℚ) * (MvPolynomial.X i - MvPolynomial.C (r i : ℚ))

theorem halvingPolynomial_support {σ : Type*} (r : σ → ℤ) (i : σ) :
    halvingPolynomial r i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  have hx : (MvPolynomial.X i : MvPolynomial σ ℚ) ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : σ => 1) (Finsupp.single i 1) (1 : ℚ)
  simpa only [halvingPolynomial, zero_add] using
    weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 (1 / 2 : ℚ))
      (Submodule.sub_mem _ hx (weightedSupportLE_C _ 1 (r i : ℚ)))

theorem halvingPolynomial_eval {σ : Type*} (r x : σ → ℤ)
    (hr : ∀ i, x i % 2 = r i) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (halvingPolynomial r i) =
      ((x i / 2 : ℤ) : ℚ) := by
  have hi : x i = 2 * (x i / 2) + r i := by
    have h := hr i
    omega
  have hiq : (x i : ℚ) = 2 * ((x i / 2 : ℤ) : ℚ) + (r i : ℚ) := by exact_mod_cast hi
  simp only [halvingPolynomial, map_mul, map_sub, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  change (1 / 2 : ℚ) * ((x i : ℚ) - (r i : ℚ)) = ((x i / 2 : ℤ) : ℚ)
  linarith

end Erdos3

end

section

namespace Erdos3

structure NativeIntegerVectorEquivalence {σ J K : Type*} [Fintype J] [Fintype K]
    (s : ℕ) (p : ℝ) (chi : J → (σ → ℤ) → ℂ) (eta : K → (σ → ℤ) → ℂ) : Prop where
  left_dimension : (Fintype.card J : ℝ) ≤ Real.exp p
  right_dimension : (Fintype.card K : ℝ) ≤ Real.exp p
  expansion : ∀ j k, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
    (fun x => chi j x * star (eta k x)))

namespace NativeIntegerVectorEquivalence

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p q : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}

theorem mono (E : NativeIntegerVectorEquivalence s p chi eta) (hpq : p ≤ q) :
    NativeIntegerVectorEquivalence s q chi eta where
  left_dimension := E.left_dimension.trans (Real.exp_le_exp.mpr hpq)
  right_dimension := E.right_dimension.trans (Real.exp_le_exp.mpr hpq)
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.mono hpq⟩

theorem symm (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p eta chi where
  left_dimension := E.right_dimension
  right_dimension := E.left_dimension
  expansion k j := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem conjugate (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p (fun j x => star (chi j x))
      (fun k x => star (eta k x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem affinePullback {τ : Type*} [Fintype τ]
    (E : NativeIntegerVectorEquivalence s p chi eta) (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => chi j (integerAffineMap A b x)) (fun k x => eta k (integerAffineMap A b x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.affinePullback A b⟩

theorem cyclicAffinePullback (E : NativeIntegerVectorEquivalence s p chi eta)
    (A : σ → Unit → ℤ) (b : σ → ℤ) (N : ℕ) [NeZero N] :
    NativeVectorEquivalence s N p
      (fun j x => chi j (integerAffineMap A b (fun _ => (x.val : ℤ))))
      (fun k x => eta k (integerAffineMap A b (fun _ => (x.val : ℤ)))) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.cyclicAffinePullback A b N⟩

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

noncomputable def selectedExpansion (j : J) (k : K) :
    NativeIntegerExpansion (fun _ : σ => 1) s p
      (fun x => chi j x * star (eta k x)) :=
  Classical.choice (E.expansion j k)

theorem transfer_sample_correlation {X : Type*} (S : Finset X) (x : X → σ → ℤ)
    (j : J) (f : X → ℂ) {q : ℝ}
    (hunit : ∀ u ∈ S, ∑ k, ‖eta k (x u)‖ ^ 2 = 1)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (chi j (x u))‖) :
    ∃ (k : K) (a : Fin (E.selectedExpansion j k).count),
      Real.exp (-(q + 2 * p)) ≤
        ‖𝔼 u ∈ S, f u * star (eta k (x u)) *
          star (((E.selectedExpansion j k).test a).eval (x u))‖ := by
  classical
  let R (k : K) := E.selectedExpansion j k
  have hexp (k : K) (u : X) (_hu : u ∈ S) :
      star (chi j (x u)) * star (star (eta k (x u))) =
        ∑ a, star ((R k).coefficient a) * star (((R k).test a).eval (x u)) := by
    have h := congrArg star ((R k).eval (x u))
    simpa only [star_sum, star_mul, star_star, mul_comm] using h
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation S f
    (fun u => star (chi j (x u))) (fun k u => star (eta k (x u)))
    (fun k a => star ((R k).coefficient a))
    (fun k a u => star (((R k).test a).eval (x u)))
    (fun u hu => by simpa only [norm_star] using hunit u hu) hexp
    (Real.exp_pos (-q)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hcorr
  have hfrac : Real.exp (-q) / (Real.exp p * Real.exp p) =
      Real.exp (-(q + 2 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  exact ⟨k, a, hka⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3

open scoped TensorProduct

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def linearPullbackHom {σ τ : Type*} [Fintype τ] {s : ℕ} {p : ℝ}
    {f : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : σ => 1) s p f)
    (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerExpansion (fun _ : τ => 1) s p (fun x => f (fun i => A i x)) :=
  { E with
    test := fun i => (E.test i).linearPullbackHom A
    complexity := E.complexity
    eval := fun x => by
      simpa only [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
        using E.eval (fun i => A i x) }

end NativeIntegerExpansion

namespace NativeIntegerVectorEquivalence

theorem linearPullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => A i x)) (fun k x => g k (fun i => A i x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.linearPullbackHom A⟩

theorem coordinatePullback {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (a : σ → τ) :
    NativeIntegerVectorEquivalence s p (fun j x => f j (fun i => x (a i)))
      (fun k x => g k (fun i => x (a i))) :=
  E.linearPullbackHom (fun i => ⟨⟨fun x => x (a i), rfl⟩, fun _ _ => rfl⟩)

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem selectedChoice_card_bound {σ I J : Type*} [Fintype I] [Fintype J]
    {s : ℕ} {p : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count) : ℝ) ≤ Real.exp (2 * p) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p := Finset.sum_le_sum (fun j _ => by
      simpa only [Fintype.card_fin] using (E.selectedExpansion i j).count_bound)
    _ = (Fintype.card J : ℝ) * Real.exp p := by simp
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, two_mul]

theorem selectedChainedChoice_card_bound {σ I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {s : ℕ} {p q : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    {h : K → (σ → ℤ) → ℂ} (E : NativeIntegerVectorEquivalence s p f g)
    (F : NativeIntegerVectorEquivalence s q g h) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count ×
      (Σ k : K, Fin (F.selectedExpansion j k).count)) : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p * Real.exp (2 * q) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      exact mul_le_mul (E.selectedExpansion i j).count_bound (F.selectedChoice_card_bound j)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card J : ℝ) * (Real.exp p * Real.exp (2 * q)) := by simp
    _ ≤ Real.exp p * (Real.exp p * Real.exp (2 * q)) :=
      mul_le_mul_of_nonneg_right E.right_dimension (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem affinePullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => b i + A i x))
      (fun k x => g k (fun i => b i + A i x)) := by
  classical
  have hinput (x : τ → ℤ) :
      integerAffineMap (fun i j => A i (Pi.single j 1)) b x = fun i => b i + A i x := by
    funext i
    rw [integerAffineMap, ← integerLinearForm_eq_sum]
  simpa only [hinput] using E.affinePullback (fun i j => A i (Pi.single j 1)) b

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
