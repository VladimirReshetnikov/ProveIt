import OAI.Combinatorics.Progressions.Estimates.ComplexExchangeTransfer
import OAI.Combinatorics.Progressions.Fourier.NiltestConjugateFrequency
import OAI.Combinatorics.Progressions.Lattices.NativeFrozenAffineExpansion
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerSelfEquivalence
import OAI.Combinatorics.Progressions.Nilpotent.NativeMultidegreeNiltest

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def boxComponent (out : Fin W.outputDim) (a b : Fin 4) :
    W.model.Niltest (fun _ : Fin 4 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

theorem boxComponent_eval (out : Fin W.outputDim) (a b : Fin 4) (n : Fin 4 → ℤ) :
    (W.boxComponent out a b).eval n = W.eval out (correlationInput (n a) (n b)) := by
  rw [boxComponent, Niltest.eval_linearPullbackHom, component_eval]
  apply congrArg (W.eval out)
  funext k
  fin_cases k <;> rfl

theorem boxComponent_vertical (out : Fin W.outputDim) (a b : Fin 4)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : W.model.Space) :
    (W.boxComponent out a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.boxComponent out a b).observable x := by
  exact W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

noncomputable def antisymmetricBoxValue (i j : Fin W.outputDim) (n : Fin 4 → ℤ) : ℂ :=
  let K := fun x y => star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)
  K (n 0) (n 2) * star (K (n 1) (n 2)) * star (K (n 0) (n 3)) * K (n 1) (n 3)

noncomputable def antisymmetricBoxFactors (i j : Fin W.outputDim) :
    Fin 8 → W.model.Niltest (fun _ : Fin 4 => 1) :=
  ![(W.boxComponent i 0 2).conjugate, W.boxComponent j 2 0,
    W.boxComponent i 1 2, (W.boxComponent j 2 1).conjugate,
    W.boxComponent i 0 3, (W.boxComponent j 3 0).conjugate,
    (W.boxComponent i 1 3).conjugate, W.boxComponent j 3 1]

noncomputable def antisymmetricBoxFrequencies : Fin 8 → (W.L →ₗ[ℚ] ℚ) :=
  ![-W.vertical.frequency, W.vertical.frequency, W.vertical.frequency, -W.vertical.frequency,
    W.vertical.frequency, -W.vertical.frequency, -W.vertical.frequency, W.vertical.frequency]

theorem antisymmetricBoxFactors_complexity (i j : Fin W.outputDim) (k : Fin 8) :
    (W.antisymmetricBoxFactors i j k).ComplexityLE (p + 8) := by
  have hi := (W.component_complexity i).mono (by linarith : p + 4 ≤ p + 8)
  have hj := (W.component_complexity j).mono (by linarith : p + 4 ≤ p + 8)
  fin_cases k
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj
  · exact hi
  · exact hj

theorem antisymmetricBoxFactors_eval (i j : Fin W.outputDim) (n : Fin 4 → ℤ) :
    (∏ k, (W.antisymmetricBoxFactors i j k).eval n) = W.antisymmetricBoxValue i j n := by
  simp [antisymmetricBoxFactors, antisymmetricBoxValue, Fin.prod_univ_succ,
    boxComponent_eval, star_mul, mul_comm, mul_left_comm]

theorem antisymmetricBoxFactors_vertical (i j : Fin W.outputDim) (k : Fin 8)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : W.model.Space) :
    (W.antisymmetricBoxFactors i j k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (W.antisymmetricBoxFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (W.antisymmetricBoxFactors i j k).observable x := by
  fin_cases k
  · exact Niltest.conjugate_vertical _ _ (W.boxComponent_vertical i 0 2) z hz x
  · exact W.boxComponent_vertical j 2 0 z hz x
  · exact W.boxComponent_vertical i 1 2 z hz x
  · exact Niltest.conjugate_vertical _ _ (W.boxComponent_vertical j 2 1) z hz x
  · exact W.boxComponent_vertical i 0 3 z hz x
  · exact Niltest.conjugate_vertical _ _ (W.boxComponent_vertical j 3 0) z hz x
  · exact Niltest.conjugate_vertical _ _ (W.boxComponent_vertical i 1 3) z hz x
  · exact W.boxComponent_vertical j 3 1 z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

noncomputable def antisymmetricBoxNiltest (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (pi (fun _ : Fin 8 => W.model)).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest (fun _ : Fin 8 => W.model) (W.antisymmetricBoxFactors i j)
    (by linarith) (by simpa using hp) (W.antisymmetricBoxFactors_complexity i j)

theorem antisymmetricBoxNiltest_complexity (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    (W.antisymmetricBoxNiltest hp i j).ComplexityLE (productNiltestBudget (p + 8)) :=
  piNiltest_complexity (fun _ : Fin 8 => W.model) (W.antisymmetricBoxFactors i j)
    (by linarith) (by simpa using hp) (W.antisymmetricBoxFactors_complexity i j)

theorem antisymmetricBoxNiltest_eval (hp : 0 ≤ p) (i j : Fin W.outputDim) (n : Fin 4 → ℤ) :
    (W.antisymmetricBoxNiltest hp i j).eval n = W.antisymmetricBoxValue i j n := by
  rw [antisymmetricBoxNiltest, piNiltest_eval]
  exact W.antisymmetricBoxFactors_eval i j n

theorem antisymmetricBoxNiltest_vertical (hp : 0 ≤ p) (i j : Fin W.outputDim)
    (z : (pi (fun _ : Fin 8 => W.model)).RealGroup)
    (hz : z ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k))
    (x : (pi (fun _ : Fin 8 => W.model)).Space) :
    (W.antisymmetricBoxNiltest hp i j).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency W.antisymmetricBoxFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (W.antisymmetricBoxNiltest hp i j).observable x :=
  piNiltest_vertical (fun _ : Fin 8 => W.model) (W.antisymmetricBoxFactors i j)
    W.antisymmetricBoxFrequencies (by linarith) (by simpa using hp)
    (W.antisymmetricBoxFactors_complexity i j) (W.antisymmetricBoxFactors_vertical i j) z hz x

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem antisymmetricBoxValue_mean (N : ℕ) [NeZero N] (i j : Fin W.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : Fin 4 => N), W.antisymmetricBoxValue i j n) =
      finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x)) := by
  have heval (k : Fin W.outputDim) (x y : ZMod N) :
      W.eval k (correlationInput (x.val : ℤ) (y.val : ℤ)) =
        W.evalCyclic N k (correlationInput x y) := by
    apply congrArg (W.eval k)
    funext l
    exact Fin.cases rfl (fun _ => rfl) l
  rw [integerBox_expect_eq_zmod]
  simp_rw [expect_fin_cons]
  unfold finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro x _
  apply Finset.expect_congr rfl
  intro x' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  change (𝔼 _ : Fin 0 → ZMod N,
    W.antisymmetricBoxValue i j ![(x.val : ℤ), (x'.val : ℤ), (y.val : ℤ), (y'.val : ℤ)]) = _
  rw [Fintype.expect_const]
  change
    (star (W.eval i (correlationInput (x.val : ℤ) (y.val : ℤ))) *
      W.eval j (correlationInput (y.val : ℤ) (x.val : ℤ))) *
    star (star (W.eval i (correlationInput (x'.val : ℤ) (y.val : ℤ))) *
      W.eval j (correlationInput (y.val : ℤ) (x'.val : ℤ))) *
    star (star (W.eval i (correlationInput (x.val : ℤ) (y'.val : ℤ))) *
      W.eval j (correlationInput (y'.val : ℤ) (x.val : ℤ))) *
    (star (W.eval i (correlationInput (x'.val : ℤ) (y'.val : ℤ))) *
      W.eval j (correlationInput (y'.val : ℤ) (x'.val : ℤ))) = _
  simp only [heval]

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

theorem antisymmetricBoxNiltest_mean (hp : 0 ≤ p) (N : ℕ) [NeZero N]
    (i j : Fin W.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : Fin 4 => N), (W.antisymmetricBoxNiltest hp i j).eval n) =
      finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x)) := by
  simp_rw [W.antisymmetricBoxNiltest_eval hp]
  exact W.antisymmetricBoxValue_mean N i j

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def antisymmetricKernel {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ℂ :=
  star (W.eval i (correlationInput x y)) * W.eval j (correlationInput y x)

theorem antisymmetricKernel_norm {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x y : ℤ) : ‖W.antisymmetricKernel i j x y‖ ≤ 1 := by
  rw [antisymmetricKernel, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i _)).trans
    (W.norm_eval j _)

theorem antisymmetricKernel_cyclic {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (N : ℕ) [NeZero N] (i j : Fin W.outputDim) (x y : ZMod N) :
    W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ) =
      star (W.evalCyclic N i (correlationInput x y)) * W.evalCyclic N j (correlationInput y x) := by
  have he (k : Fin W.outputDim) (x y : ZMod N) :
      W.eval k (correlationInput (x.val : ℤ) (y.val : ℤ)) =
        W.evalCyclic N k (correlationInput x y) := by
    apply congrArg (W.eval k)
    funext l
    fin_cases l <;> rfl
  simp only [antisymmetricKernel, he]

theorem antisymmetricKernel_box {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x : Fin 4 → ℤ) :
    boxKernel (W.antisymmetricKernel i j) x = W.antisymmetricBoxValue i j x := rfl

theorem exists_mixed_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (d : Fin 2) (c : ℤ) (k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => W.eval k (Function.update (fun _ => c) d (x ())))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_frozen_affine_expansion (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W d c k
  classical
  let A : Fin 2 → ℤ := fun j => if j = d then 1 else 0
  let b : Fin 2 → ℤ := fun j => if j = d then 0 else c
  obtain ⟨E, _⟩ := hfreeze W {d} A b k (by
    intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [A, hj])
  have hdegree : (∑ j ∈ ({d} : Finset (Fin 2)), mixedCorrelationDegree 1 j) = 1 := by
    simp only [Finset.sum_singleton]
    fin_cases d <;> rfl
  have heq : (fun x : Unit → ℤ => W.eval k (fun j => b j + A j * x ())) =
      (fun x => W.eval k (Function.update (fun _ => c) d (x ()))) := by
    funext x
    apply congrArg (W.eval k)
    funext j
    by_cases hj : j = d
    · subst j
      simp [A, b]
    · simp [A, b, hj]
  exact ⟨by simpa only [hdegree, heq] using E⟩

theorem exists_antisymmetric_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (d : Fin 2) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 ((p + C) ^ C)
        (fun x => let z := Function.update (fun _ => c) d (x ())
          W.antisymmetricKernel i j (z 0) (z 1))) := by
  obtain ⟨A, _, hslice⟩ := exists_mixed_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := hslice W d c i
  obtain ⟨F⟩ := hslice W d.rev c j
  obtain ⟨G⟩ := hmul (by positivity : 0 ≤ (p + A) ^ A) E.conjugate F
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have heq : (fun x : Unit → ℤ => star (W.eval i (Function.update (fun _ => c) d (x ()))) *
      W.eval j (Function.update (fun _ => c) d.rev (x ()))) =
      (fun x => let z := Function.update (fun _ => c) d (x ())
        W.antisymmetricKernel i j (z 0) (z 1)) := by
    funext x
    unfold antisymmetricKernel
    congr 1
    · congr 1
      apply congrArg (W.eval i)
      funext l
      fin_cases l <;> rfl
    · apply congrArg (W.eval j)
      funext l
      fin_cases d <;> fin_cases l <;> rfl
  exact ⟨by simpa only [heq] using G.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_mixed_self_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C) W.eval W.eval := by
  have hbound : mixedCorrelationDegree 1 = (fun _ : Fin 2 => 1) := by
    funext i
    fin_cases i <;> rfl
  rw [hbound]
  simpa using (exists_integer_self_equivalence (σ := Fin 2))

noncomputable def coordinateTransfer {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j k l : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  exchangeTransfer (fun r => W.eval r x) (fun r => W.eval r (fun h => x h.rev)) i j k l

theorem antisymmetricKernel_tuple {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.antisymmetricKernel i j (x 0) (x 1) =
      star (W.eval i x) * W.eval j (fun h => x h.rev) := by
  have hxy : correlationInput (x 0) (x 1) = x := by
    funext h
    fin_cases h <;> rfl
  have hyx : correlationInput (x 1) (x 0) = (fun h : Fin 2 => x h.rev) := by
    funext h
    fin_cases h <;> rfl
  simp only [antisymmetricKernel, hxy, hyx]

theorem coordinateTransfer_diagonal {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.coordinateTransfer i j i j x = (‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2 : ℝ) := by
  rw [coordinateTransfer, exchange_transfer_diagonal, W.antisymmetricKernel_tuple]

theorem coordinateTransfer_matrix_error {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
    (i j : Fin W.outputDim) (x : Fin 2 → ℤ) (w : ℝ) (g : ℂ) :
    Real.sqrt (∑ k, ∑ l,
      ‖W.antisymmetricKernel k l (x 0) (x 1) *
          (w * ‖W.antisymmetricKernel i j (x 0) (x 1)‖ ^ 2 : ℝ) -
        g * W.coordinateTransfer i j k l x‖ ^ 2) ≤
      ‖W.antisymmetricKernel i j (x 0) (x 1) * (w : ℂ) - g‖ := by
  simpa only [W.antisymmetricKernel_tuple, coordinateTransfer] using
    exchange_matrix_error_le (fun r => W.eval r x) (fun r => W.eval r (fun h => x h.rev))
      (W.unit_eval x) (W.unit_eval (fun h => x h.rev)) i j
      (W.norm_eval i x) (W.norm_eval j (fun h => x h.rev)) w g

theorem exists_coordinate_transfer_expansions :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j k l : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (W.coordinateTransfer i j k l)) := by
  obtain ⟨A, _, hself⟩ := exists_mixed_self_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j k l
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  obtain ⟨E⟩ := (hself W).expansion i k
  obtain ⟨F⟩ := (hself W).expansion l j
  let F' := F.linearPullbackHom (fun h : Fin 2 =>
    { toFun := fun x : Fin 2 → ℤ => x h.rev, map_zero' := rfl, map_add' := fun _ _ => rfl })
  obtain ⟨G⟩ := hmul (by positivity : 0 ≤ (p + A) ^ A) E F'
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨G.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
