import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricModel

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicBoxComponent (out : Fin V.outputDim) (h y k : Fin 6) (shift : ℤ) :
    V.model.Niltest (fun _ : Fin 6 => 1) :=
  (V.component out).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

theorem cubicBoxComponent_eval (out : Fin V.outputDim) (h y k : Fin 6) (shift : ℤ) (n : Fin 6 → ℤ) :
    (V.cubicBoxComponent out h y k shift).eval n =
      V.eval out (cubicTrilinearInput (n h) (n y) (n k + shift)) := by
  rw [cubicBoxComponent, Niltest.eval_affinePullback, component_eval]
  apply congrArg (V.eval out)
  funext j
  rcases j with ⟨j, a⟩
  fin_cases j <;> fin_cases a <;>
    simp [integerAffineMap, cubicTrilinearInput, ite_mul, add_comm]

theorem cubicBoxComponent_vertical (out : Fin V.outputDim) (h y k : Fin 6) (shift : ℤ)
    (z : V.model.RealGroup)
    (hz : z ∈ V.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : V.model.Space) :
    (V.cubicBoxComponent out h y k shift).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional V.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (V.cubicBoxComponent out h y k shift).observable x := by
  exact V.vertical.vertical out z (by rwa [V.multi.realSubgroup_top]) x

noncomputable def cubicKernelFactors (i j : Fin V.outputDim × Fin V.outputDim)
    (h y k : Fin 6) (shift : ℤ) : Fin 4 → V.model.Niltest (fun _ : Fin 6 => 1) :=
  ![(V.cubicBoxComponent i.1 h y k shift).conjugate, V.cubicBoxComponent j.1 y h k shift,
    (V.cubicBoxComponent i.2 h y k shift).conjugate, V.cubicBoxComponent j.2 y h k shift]

noncomputable def cubicKernelFrequencies : Fin 4 → (V.L →ₗ[ℚ] ℚ) :=
  ![-V.vertical.frequency, V.vertical.frequency, -V.vertical.frequency, V.vertical.frequency]

theorem cubicKernelFactors_complexity (i j : Fin V.outputDim × Fin V.outputDim)
    (h y k : Fin 6) (shift : ℤ) (a : Fin 4) :
    (V.cubicKernelFactors i j h y k shift a).ComplexityLE (p + 32) := by
  have hi₁ := (V.component_complexity i.1).mono (by linarith : p + 4 ≤ p + 32)
  have hj₁ := (V.component_complexity j.1).mono (by linarith : p + 4 ≤ p + 32)
  have hi₂ := (V.component_complexity i.2).mono (by linarith : p + 4 ≤ p + 32)
  have hj₂ := (V.component_complexity j.2).mono (by linarith : p + 4 ≤ p + 32)
  fin_cases a
  · exact hi₁
  · exact hj₁
  · exact hi₂
  · exact hj₂

theorem cubicKernelFactors_eval (i j : Fin V.outputDim × Fin V.outputDim)
    (h y k : Fin 6) (shift : ℤ) (n : Fin 6 → ℤ) :
    (∏ a, (V.cubicKernelFactors i j h y k shift a).eval n) =
      V.cubicAntisymmetricPair i j (n h) (n y) (n k + shift) := by
  simp [cubicKernelFactors, Fin.prod_univ_succ, cubicBoxComponent_eval,
    cubicAntisymmetricPair, mul_assoc]

theorem cubicKernelFactors_vertical (i j : Fin V.outputDim × Fin V.outputDim)
    (h y k : Fin 6) (shift : ℤ) (a : Fin 4) (z : V.model.RealGroup)
    (hz : z ∈ V.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : V.model.Space) :
    (V.cubicKernelFactors i j h y k shift a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.cubicKernelFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (V.cubicKernelFactors i j h y k shift a).observable x := by
  fin_cases a
  · exact Niltest.conjugate_vertical _ _ (V.cubicBoxComponent_vertical i.1 h y k shift) z hz x
  · exact V.cubicBoxComponent_vertical j.1 y h k shift z hz x
  · exact Niltest.conjugate_vertical _ _ (V.cubicBoxComponent_vertical i.2 h y k shift) z hz x
  · exact V.cubicBoxComponent_vertical j.2 y h k shift z hz x

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

def cubicBoxCorner : Fin 8 → Fin 3 → Fin 6 :=
  ![![2, 4, 0], ![2, 4, 1], ![3, 4, 0], ![3, 4, 1],
    ![2, 5, 0], ![2, 5, 1], ![3, 5, 0], ![3, 5, 1]]

def cubicBoxConjugated : Fin 8 → Bool :=
  ![false, true, true, false, true, false, false, true]

variable {p : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicAntisymmetricBoxValue (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (n : Fin 6 → ℤ) : ℂ :=
  let F := fun k h y => V.cubicAntisymmetricPair i j h y (k + shift)
  let G := fun h y => F (n 0) h y * star (F (n 1) h y)
  G (n 2) (n 4) * star (G (n 3) (n 4)) * star (G (n 2) (n 5)) * G (n 3) (n 5)

noncomputable def cubicAntisymmetricBoxFactors (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (a : Fin 8 × Fin 4) : V.model.Niltest (fun _ : Fin 6 => 1) :=
  let T := V.cubicKernelFactors i j (cubicBoxCorner a.1 0) (cubicBoxCorner a.1 1)
    (cubicBoxCorner a.1 2) shift a.2
  if cubicBoxConjugated a.1 then T.conjugate else T

noncomputable def cubicAntisymmetricBoxFrequencies (a : Fin 8 × Fin 4) : V.L →ₗ[ℚ] ℚ :=
  if cubicBoxConjugated a.1 then -V.cubicKernelFrequencies a.2 else V.cubicKernelFrequencies a.2

theorem cubicAntisymmetricBoxFactors_complexity (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (a : Fin 8 × Fin 4) :
    (V.cubicAntisymmetricBoxFactors i j shift a).ComplexityLE (p + 32) := by
  unfold cubicAntisymmetricBoxFactors
  split <;> exact V.cubicKernelFactors_complexity i j _ _ _ shift a.2

theorem cubicAntisymmetricBoxFactors_eval (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (n : Fin 6 → ℤ) :
    (∏ a, (V.cubicAntisymmetricBoxFactors i j shift a).eval n) =
      V.cubicAntisymmetricBoxValue i j shift n := by
  have hrow (c : Fin 8) : (∏ a : Fin 4, (V.cubicAntisymmetricBoxFactors i j shift (c, a)).eval n) =
      if cubicBoxConjugated c then
        star (V.cubicAntisymmetricPair i j (n (cubicBoxCorner c 0)) (n (cubicBoxCorner c 1))
          (n (cubicBoxCorner c 2) + shift)) else
        V.cubicAntisymmetricPair i j (n (cubicBoxCorner c 0)) (n (cubicBoxCorner c 1))
          (n (cubicBoxCorner c 2) + shift) := by
    cases hsign : cubicBoxConjugated c with
    | false =>
      simpa only [cubicAntisymmetricBoxFactors, hsign, Bool.false_eq_true, ite_false] using
        V.cubicKernelFactors_eval i j (cubicBoxCorner c 0) (cubicBoxCorner c 1)
          (cubicBoxCorner c 2) shift n
    | true =>
      simpa only [cubicAntisymmetricBoxFactors, hsign, ite_true, Niltest.eval_conjugate,
        star_prod] using congrArg star
          (V.cubicKernelFactors_eval i j (cubicBoxCorner c 0) (cubicBoxCorner c 1)
            (cubicBoxCorner c 2) shift n)
  rw [Fintype.prod_prod_type]
  simp_rw [hrow]
  simp [Fin.prod_univ_succ, cubicBoxCorner, cubicBoxConjugated,
    cubicAntisymmetricBoxValue, star_mul, mul_comm, mul_left_comm]

theorem cubicAntisymmetricBoxFactors_vertical (i j : Fin V.outputDim × Fin V.outputDim)
    (shift : ℤ) (a : Fin 8 × Fin 4) (z : V.model.RealGroup)
    (hz : z ∈ V.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : V.model.Space) :
    (V.cubicAntisymmetricBoxFactors i j shift a).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.cubicAntisymmetricBoxFrequencies a) z.coord : ℝ) : CircleFourier.Circle) *
          (V.cubicAntisymmetricBoxFactors i j shift a).observable x := by
  unfold cubicAntisymmetricBoxFactors cubicAntisymmetricBoxFrequencies
  split_ifs
  · exact Niltest.conjugate_vertical _ _ (V.cubicKernelFactors_vertical i j _ _ _ shift a.2) z hz x
  · exact V.cubicKernelFactors_vertical i j _ _ _ shift a.2 z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]

noncomputable def cubicAntisymmetricBoxNiltest (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) :
    (pi (fun _ : Fin 8 × Fin 4 => V.model)).Niltest (fun _ : Fin 6 => 1) :=
  piNiltest (fun _ : Fin 8 × Fin 4 => V.model) (V.cubicAntisymmetricBoxFactors i j shift)
    (by linarith) (by simpa using (show (32 : ℝ) ≤ p + 32 by linarith))
    (V.cubicAntisymmetricBoxFactors_complexity i j shift)

theorem cubicAntisymmetricBoxNiltest_complexity (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) :
    (V.cubicAntisymmetricBoxNiltest hp i j shift).ComplexityLE (productNiltestBudget (p + 32)) :=
  piNiltest_complexity (fun _ : Fin 8 × Fin 4 => V.model) (V.cubicAntisymmetricBoxFactors i j shift)
    (by linarith) (by simpa using (show (32 : ℝ) ≤ p + 32 by linarith))
    (V.cubicAntisymmetricBoxFactors_complexity i j shift)

theorem cubicAntisymmetricBoxNiltest_eval (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) (n : Fin 6 → ℤ) :
    (V.cubicAntisymmetricBoxNiltest hp i j shift).eval n = V.cubicAntisymmetricBoxValue i j shift n := by
  rw [cubicAntisymmetricBoxNiltest, piNiltest_eval]
  exact V.cubicAntisymmetricBoxFactors_eval i j shift n

theorem cubicAntisymmetricBoxNiltest_vertical (hp : 0 ≤ p)
    (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ)
    (z : (pi (fun _ : Fin 8 × Fin 4 => V.model)).RealGroup)
    (hz : z ∈ (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.realification.subgroup
      (∑ _ : CubicReplicatedIndex, 1))
    (x : (pi (fun _ : Fin 8 × Fin 4 => V.model)).Space) :
    (V.cubicAntisymmetricBoxNiltest hp i j shift).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.cubicAntisymmetricBoxFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.cubicAntisymmetricBoxNiltest hp i j shift).observable x :=
  piNiltest_vertical (fun _ : Fin 8 × Fin 4 => V.model) (V.cubicAntisymmetricBoxFactors i j shift)
    V.cubicAntisymmetricBoxFrequencies (by linarith)
    (by simpa using (show (32 : ℝ) ≤ p + 32 by linarith))
    (V.cubicAntisymmetricBoxFactors_complexity i j shift)
    (V.cubicAntisymmetricBoxFactors_vertical i j shift) z hz x

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_antisymmetric_box :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim × Fin V.outputDim),
              Real.exp (-((p + C) ^ C)) ≤
                (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
                  V.cubicAntisymmetricPair i' j' h.val y.val (cyclicBranchOffset k branch))).re := by
  obtain ⟨a, _, hanti⟩ := exists_cubic_antisymmetric_model
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (8 * Q + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : 8 * q + 2 ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have hcost : 8 * q ≤ (p + C) ^ C := by linarith only [hsum]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', A, B, D, hA, hB, hD, hanti⟩ :=
    hanti hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let F (k h y : ZMod N) := V.cubicAntisymmetricPair i' j' h.val y.val (cyclicBranchOffset k branch)
  have heq (k h y : ZMod N) :
      F k h y * A h.val (cyclicBranchOffset k branch) * D h.val y.val * B y.val (cyclicBranchOffset k branch) =
      F k h y * A h.val (cyclicBranchOffset k branch) * B y.val (cyclicBranchOffset k branch) * D h.val y.val := by
    ring
  have hbox := norm_pairwise_weighted_mean_pow_eight_le_box F
    (fun k h => A h.val (cyclicBranchOffset k branch)) (fun h y => D h.val y.val)
    (fun k y => B y.val (cyclicBranchOffset k branch))
    (fun k h => hA _ _) (fun h y => hD _ _) (fun k y => hB _ _)
  simp only [heq] at hbox
  have hbound := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hanti 8).trans hbox
  have hpower : Real.exp (-q) ^ 8 = Real.exp (-(8 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hbound
  have heval : (fun k h y : ZMod N => (V.mono hqC).cubicAntisymmetricPair i' j'
      h.val y.val (cyclicBranchOffset k branch)) = F := by
    funext k h y
    simp only [F, NativeMultidegreeNilcharacter.cubicAntisymmetricPair,
      NativeMultidegreeNilcharacter.mono_eval]
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · rw [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hbound

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

theorem cubicAntisymmetricBoxValue_mean (N : ℕ) [NeZero N] (branch : Bool)
    (i j : Fin V.outputDim × Fin V.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : Fin 6 => N),
      V.cubicAntisymmetricBoxValue i j (-(if branch then (N : ℤ) else 0)) n) =
      finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        V.cubicAntisymmetricPair i j h.val y.val (cyclicBranchOffset k branch)) := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [expect_fin_cons]
  unfold finiteTripleBoxCorrelation finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro k _
  apply Finset.expect_congr rfl
  intro k' _
  apply Finset.expect_congr rfl
  intro h _
  apply Finset.expect_congr rfl
  intro h' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  change (𝔼 _ : Fin 0 → ZMod N,
    V.cubicAntisymmetricBoxValue i j (-(if branch then (N : ℤ) else 0))
      ![(k.val : ℤ), (k'.val : ℤ), (h.val : ℤ), (h'.val : ℤ), (y.val : ℤ), (y'.val : ℤ)]) = _
  rw [Fintype.expect_const]
  simp only [cubicAntisymmetricBoxValue, cyclicBranchOffset, sub_eq_add_neg,
    show (5 : Fin 6) = (4 : Fin 5).succ by rfl, Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

variable [TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]

theorem cubicAntisymmetricBoxNiltest_mean (hp : 0 ≤ p) (N : ℕ) [NeZero N] (branch : Bool)
    (i j : Fin V.outputDim × Fin V.outputDim) :
    (𝔼 n ∈ integerBox (fun _ : Fin 6 => N),
      (V.cubicAntisymmetricBoxNiltest hp i j (-(if branch then (N : ℤ) else 0))).eval n) =
      finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        V.cubicAntisymmetricPair i j h.val y.val (cyclicBranchOffset k branch)) := by
  simp_rw [V.cubicAntisymmetricBoxNiltest_eval hp]
  exact V.cubicAntisymmetricBoxValue_mean N branch i j

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeCubicBoxFactorization {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin V.outputDim × Fin V.outputDim
  rightIndex : Fin V.outputDim × Fin V.outputDim
  branch : Bool
  nonnegative : 0 ≤ p
  [topology : TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  [hausdorff : T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L))]
  basis : Basis (Fin (finrank ℚ ((Fin 8 × Fin 4) → V.L))) ℚ ((Fin 8 × Fin 4) → V.L)
  weight : Fin (finrank ℚ ((Fin 8 × Fin 4) → V.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  height : ∀ i j, rationalLogHeight
    ((pi (fun _ : Fin 8 × Fin 4 => V.model)).basis.repr (basis i) j) ≤ q
  factorization : (pi (fun _ : Fin 8 × Fin 4 => V.model)).filtration.ControlledSymbolFactorization
    basis weight adapted (piFrequency V.cubicAntisymmetricBoxFrequencies) (fun _ : Fin 6 => (N : ℝ))
    ((V.cubicAntisymmetricBoxNiltest nonnegative leftIndex rightIndex
      (-(if branch then (N : ℤ) else 0))).symbol basis weight adapted) q

theorem exists_cubic_box_step_drop_indices :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
        {N : ℕ} [NeZero N] (branch : Bool) (i j : Fin V.outputDim × Fin V.outputDim),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ (finiteTripleBoxCorrelation (fun k h y : ZMod N =>
        V.cubicAntisymmetricPair i j h.val y.val (cyclicBranchOffset k branch))).re →
      ∃ R : NativeCubicBoxFactorization V N ((p + C) ^ C),
        R.leftIndex = i ∧ R.rightIndex = j ∧ R.branch = branch := by
  have hdegree : (∑ _ : CubicReplicatedIndex, (1 : ℕ)) = 3 := by
    have hc : Fintype.card CubicReplicatedIndex = 3 := by
      calc
        _ = ∑ i : Fin 2, mixedCorrelationDegree 2 i := replicatedIndex_card _
        _ = 3 := by rw [Fin.sum_univ_two]; rfl
    simpa using hc
  obtain ⟨a, _, hstep⟩ := exists_intrinsic_step_drop (∑ _ : CubicReplicatedIndex, 1) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 32
  let R := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 6
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + 1 + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp V N _ branch i j hN hbox
  let r := productNiltestBudget (p + 32) + p + 6
  have hprod : 0 ≤ productNiltestBudget (p + 32) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith only [hprod]
  have h6r : 6 ≤ r := by dsimp only [r]; linarith only [hprod, hp]
  have hTr : productNiltestBudget (p + 32) ≤ r := by dsimp only [r]; linarith only [hp]
  have hr : 0 ≤ r := hp.trans hpr
  have hcost : r + 1 + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, R, r, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hheight : r + 1 ≤ (p + C) ^ C := by linarith only [hcost, hpow]
  have hfactor : (r + a) ^ a ≤ (p + C) ^ C := by linarith only [hcost, hr]
  obtain ⟨τ, htA, htM, htT⟩ := exists_real_module_topology
    (productFinBasis (fun _ : Fin 8 × Fin 4 => V.model))
  let : TopologicalSpace (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L)) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L)) := htA
  let : ContinuousSMul ℝ (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L)) := htM
  let : T2Space (ℝ ⊗[ℚ] ((Fin 8 × Fin 4) → V.L)) := htT
  let D := pi (fun _ : Fin 8 × Fin 4 => V.model)
  let T := V.cubicAntisymmetricBoxNiltest hp i j (-(if branch then (N : ℤ) else 0))
  obtain ⟨e, ω, hF, he, hconstruct⟩ := hstep D hr T
    ((V.cubicAntisymmetricBoxNiltest_complexity hp i j _).mono hTr)
  have hbias : Real.exp (-r) ≤ ‖𝔼 n ∈ translatedIntegerBox 0 (fun _ : Fin 6 => N), T.eval n‖ := by
    have hzero : translatedIntegerBox 0 (fun _ : Fin 6 => N) = integerBox (fun _ : Fin 6 => N) := by
      ext n
      simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
    rw [hzero, show T = V.cubicAntisymmetricBoxNiltest hp i j (-(if branch then (N : ℤ) else 0)) from rfl,
      V.cubicAntisymmetricBoxNiltest_mean]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans (hbox.trans (Complex.re_le_norm _))
  have hf := hconstruct (piFrequency V.cubicAntisymmetricBoxFrequencies)
    (V.cubicAntisymmetricBoxNiltest_vertical hp i j _) 0 (fun _ : Fin 6 => N)
    (fun _ => NeZero.pos N) (by simpa using h6r)
    (fun _ => (Real.exp_le_exp.mpr hfactor).trans hN) hbias
  exact ⟨{
    leftIndex := i
    rightIndex := j
    branch := branch
    nonnegative := hp
    topology := τ
    topologicalAdd := htA
    continuousSMul := htM
    hausdorff := htT
    basis := e
    weight := ω
    adapted := hF
    height := fun i j => (he i j).trans hheight
    factorization := NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration e ω hF hf hfactor (fun _ => by exact_mod_cast NeZero.pos N) }, rfl, rfl, rfl⟩

end Erdos3

end

end OAI
