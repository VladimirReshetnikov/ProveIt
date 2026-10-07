import OAI.Combinatorics.Progressions.Geometry.QuadraticAntisymmetricBox

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_antisymmetric_anchor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      (i j : Fin W.outputDim) (a : Fin 2 → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        (boxAnchorFactor (W.antisymmetricKernel i j) a)) := by
  obtain ⟨A, _, hslice⟩ := exists_antisymmetric_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := Q + (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  let r := q + (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := le_add_of_nonneg_right (by positivity)
  have hbr : (q + B) ^ B ≤ r := le_add_of_nonneg_left hq
  obtain ⟨Ex⟩ := hslice W i j 0 (a 1)
  obtain ⟨Ey⟩ := hslice W i j 1 (a 0)
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (x ()) (a 1)) at Ex
  change NativeIntegerExpansion (fun _ : Unit => 1) 1 q
    (fun x => W.antisymmetricKernel i j (a 0) (x ())) at Ey
  let Ex' := Ex.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 0, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  let Ey' := Ey.linearPullbackHom (fun _ : Unit =>
    ({ toFun := fun z : Fin 2 → ℤ => z 1, map_zero' := rfl, map_add' := fun _ _ => rfl }))
  have Ec : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q
      (fun _ => W.antisymmetricKernel i j (a 0) (a 1)) := by
    simpa [integerAffineMap] using Ex.affinePullback
      (fun (_ : Unit) (_ : Fin 2) => (0 : ℤ)) (fun _ => a 0)
  obtain ⟨E⟩ := hmul hq Ey'.conjugate Ex'.conjugate
  obtain ⟨F⟩ := hmul hr (E.mono hbr) (Ec.mono hqr)
  have hcost : (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [R, Q, X, r, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.boxSlice {s : ℕ} {p : ℝ}
    {F : (Fin 4 → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : Fin 4 => 1) s p F)
    (a : Fin 2 → ℤ) : NativeIntegerExpansion (fun _ : Fin 2 => 1) s p
      (fun z => F (Erdos3.boxSlice a z)) := by
  let A : Fin 4 → Fin 2 → ℤ := ![![1, 0], ![0, 0], ![0, 1], ![0, 0]]
  let b : Fin 4 → ℤ := ![0, a 0, 0, a 1]
  have hmap (z : Fin 2 → ℤ) : integerAffineMap A b z = Erdos3.boxSlice a z := by
    funext i
    fin_cases i <;> norm_num [A, b, integerAffineMap, Erdos3.boxSlice, Fin.sum_univ_two]
  have heq : (fun z => F (integerAffineMap A b z)) = (fun z => F (Erdos3.boxSlice a z)) := by
    funext z
    rw [hmap]
  exact heq ▸ E.affinePullback A b

theorem exists_antisymmetric_pair_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (i j : Fin W.outputDim) (F : (Fin 4 → ℤ) → ℂ),
      0 ≤ q → NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 q F →
      ∀ {δ ε : ℝ}, 0 < δ → 0 < ε →
      δ ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ))).re →
      (𝔼 x : Fin 4 → ZMod N,
        ‖W.antisymmetricBoxValue i j (fun k => ((x k).val : ℤ)) -
          F (fun k => ((x k).val : ℤ))‖) ≤ ε →
      ∃ D G : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C) D) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C) G) ∧
        (∀ z, ‖D z‖ ≤ 1) ∧
        δ ^ 2 / 2 ≤ (𝔼 z : Fin 2 → ZMod N, ‖D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
        δ ^ 2 / 2 ≤ (𝔼 z : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
            D (fun k => ((z k).val : ℤ))‖ ^ 2) ∧
        (𝔼 z : Fin 2 → ZMod N,
          ‖W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
              D (fun k => ((z k).val : ℤ)) - G (fun k => ((z k).val : ℤ))‖) ≤
          2 * ε / δ ^ 2 := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_antisymmetric_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ i j F hq EF δ ε hδ hε hbias herr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let K := fun x y : ZMod N => W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ)
  let Fc := fun x : Fin 4 → ZMod N => F (fun k => ((x k).val : ℤ))
  obtain ⟨a, hmass, henergy, herror⟩ := exists_box_anchor_approximation K
    (fun x y => W.antisymmetricKernel_norm i j _ _) Fc hδ hε hbias herr
  let b : Fin 2 → ℤ := fun k => ((a k).val : ℤ)
  let D := boxAnchorFactor (W.antisymmetricKernel i j) b
  let G := fun z : Fin 2 → ℤ => F (boxSlice b z)
  obtain ⟨ED⟩ := hanchor W i j b
  have hsum : (p + q + A) ^ A + (p + q) ≤ (p + q + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget (p + q) (add_nonneg hp hq)
  have hDb : (p + A) ^ A ≤ (p + q + C) ^ C := by
    have hmono : (p + A) ^ A ≤ (p + q + A) ^ A := by gcongr; linarith
    exact hmono.trans ((le_add_of_nonneg_right (add_nonneg hp hq)).trans hsum)
  have hGb : q ≤ (p + q + C) ^ C := by
    have hpow : 0 ≤ (p + q + A) ^ A := by positivity
    linarith
  have hcan (z : Fin 2 → ZMod N) :
      (fun k => ((boxSlice a z k).val : ℤ)) = boxSlice b (fun k => ((z k).val : ℤ)) := by
    funext k
    fin_cases k <;> rfl
  refine ⟨D, G, ⟨ED.mono hDb⟩, ⟨(EF.boxSlice b).mono hGb⟩, ?_, hmass, henergy, ?_⟩
  · exact boxAnchorFactor_norm_le_one _ (W.antisymmetricKernel_norm i j) b
  · simpa only [Fc, hcan, K, D, G, boxAnchorFactor, b] using herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_antisymmetric_pair_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}, 0 ≤ p →
      ∀ (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
        {N : ℕ} [NeZero N] (i j : Fin W.outputDim),
      Real.exp (-p) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
        star (W.evalCyclic N i (correlationInput x y)) *
          W.evalCyclic N j (correlationInput y x))).re →
      Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hanchor⟩ := NativeMultidegreeNilcharacter.exists_antisymmetric_anchor_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro p hp W N _ i j hbox
  let K (x y : ZMod N) := W.antisymmetricKernel i j (x.val : ℤ) (y.val : ℤ)
  have hbias : Real.exp (-p) ≤ (finiteBoxCorrelation K).re := by
    simpa only [K, W.antisymmetricKernel_cyclic] using hbox
  obtain ⟨a, ha⟩ := exists_box_anchor_correlation K
  obtain ⟨E⟩ := hanchor W i j (fun k => ((a k).val : ℤ))
  have hcorr : Real.exp (-p) ≤ ‖𝔼 z : Fin 2 → ZMod N,
      W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ) *
        star (star (boxAnchorFactor (W.antisymmetricKernel i j)
          (fun k => ((a k).val : ℤ)) (fun k => ((z k).val : ℤ))))‖ := by
    simpa only [K, boxAnchorFactor, star_star] using hbias.trans ha
  obtain ⟨V⟩ := NativeSampleCorrelation.exists_of_expansion E.conjugate hp hcorr
  have hcost : p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨V.mono hcost⟩

end Erdos3

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

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponent (out : Fin W.outputDim) (a b : Fin 2) :
    W.model.Niltest (fun _ : Fin 2 => 1) :=
  (W.component out).linearPullbackHom
    ![{ toFun := fun n => n a, map_zero' := rfl, map_add' := fun _ _ => rfl },
      { toFun := fun n => n b, map_zero' := rfl, map_add' := fun _ _ => rfl }]

theorem pairComponent_eval (out : Fin W.outputDim) (a b : Fin 2) (n : Fin 2 → ℤ) :
    (W.pairComponent out a b).eval n = W.eval out (correlationInput (n a) (n b)) := by
  rw [pairComponent, Niltest.eval_linearPullbackHom, component_eval]
  apply congrArg (W.eval out)
  funext k
  fin_cases k <;> rfl

theorem pairComponent_vertical (out : Fin W.outputDim) (a b : Fin 2)
    (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ k, mixedCorrelationDegree 1 k))
    (x : W.model.Space) :
    (W.pairComponent out a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.pairComponent out a b).observable x :=
  W.vertical.vertical out z (by rwa [W.multi.realSubgroup_top]) x

end NativeMultidegreeNilcharacter

def antisymmetricPairBudget (p q : ℝ) : ℝ := p + q + raisedNiltestBudget (p + q) + 4

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

abbrev AntisymmetricPairAlgebra :=
  ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def antisymmetricPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ l, mixedCorrelationDegree 1 l) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def antisymmetricPairTests :
    ∀ k, (V.antisymmetricPairModels k).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![(W.pairComponent i 0 1).conjugate, W.pairComponent j 1 0] k

noncomputable def antisymmetricPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-W.vertical.frequency, W.vertical.frequency] k

theorem antisymmetricPairTests_eval (n : Fin 2 → ℤ) :
    (∏ k, (V.antisymmetricPairTests k).eval n) =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by decide : 1 ≤ ∑ l, mixedCorrelationDegree 1 l)).conjugate.eval n *
    ((W.pairComponent i 0 1).conjugate.eval n * (W.pairComponent j 1 0).eval n) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.pairComponent_eval, W.pairComponent_eval]
  unfold NativeMultidegreeNilcharacter.antisymmetricKernel
  ring

theorem antisymmetricPairTests_vertical (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l))
    (x : (V.antisymmetricPairModels k).Space) :
    (V.antisymmetricPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.antisymmetricPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by decide : 1 < ∑ l, mixedCorrelationDegree 1 l) z hz x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical i 0 1) z hz x
    · exact W.pairComponent_vertical j 1 0 z hz x

include V in
theorem antisymmetricPairBudget_four_le : 4 ≤ antisymmetricPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold antisymmetricPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem antisymmetricPairTests_complexity (k : Option (Fin 2)) :
    (V.antisymmetricPairTests k).ComplexityLE (antisymmetricPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by decide) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold antisymmetricPairBudget; linarith)
  | some k =>
    have hcost : p + 4 ≤ antisymmetricPairBudget p q := by
      unfold antisymmetricPairBudget
      linarith
    fin_cases k
    · exact (W.component_complexity i).mono hcost
    · exact (W.component_complexity j).mono hcost

end NativeSampleCorrelation

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_correlator :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                Nonempty (NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ))) := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_antisymmetric_box
  obtain ⟨B, _, hpair⟩ := exists_antisymmetric_pair_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hcost
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', hbias⟩ := hbox hp f hf hG
  obtain ⟨V⟩ := hpair hq M i' j' hbias
  exact ⟨q, hq, hqC, H, hH, hdense, M, i, hcorr, i', j', ⟨V.mono hBC⟩⟩

end Erdos3

end

end OAI
