import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_cubic_frozen_affine_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (d : CubicReplicatedIndex) (A : CubicReplicatedIndex → Fin 3 → ℤ)
      (b : CubicReplicatedIndex → ℤ) (out : Fin V.outputDim),
      (∀ k, A d k = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
        (fun x => V.eval out (integerAffineMap A b x))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest (fun _ : CubicReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p V d A b out hA
  classical
  let S : Finset CubicReplicatedIndex := Finset.univ.erase d
  have hcard : Fintype.card CubicReplicatedIndex = 3 := by
    calc
      _ = ∑ j : Fin 2, mixedCorrelationDegree 2 j := replicatedIndex_card _
      _ = 3 := by rw [Fin.sum_univ_two]; rfl
  have hdegree : (∑ j ∈ S, (1 : ℕ)) = 2 := by simp [S, hcard]
  obtain ⟨t, n, ht, _hn, D, hD⟩ := hfreeze V S b out
  have ht2 : t = 2 := ht.trans hdegree
  rcases ht2 with rfl
  let K := V.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _hTnorm, hT, _hzero, heval⟩ := hD
  let U := T.affinePullback (fun j k => A j.val k) (fun j => b j.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hvalue (x : Fin 3 → ℤ) : U.eval x = V.eval out (integerAffineMap A b x) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    apply congrArg (V.eval out)
    funext j
    by_cases hj : j ∈ S
    · simp [freezeCoordinates, hj, integerAffineMap]
    · have hjd : j = d := by simpa [S] using hj
      subst j
      simp [freezeCoordinates, hj, integerAffineMap, hA]
  let E : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + C) ^ C) U.eval :=
    NativeIntegerExpansion.ofTest U hU (fun _ => rfl)
  have heq : U.eval = (fun x => V.eval out (integerAffineMap A b x)) := funext hvalue
  exact ⟨heq ▸ E⟩

theorem exists_cubic_scalar_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (out : Fin V.outputDim) (d : Fin 3) (c shift : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          V.eval out (cubicTrilinearInput (z 1) (z 2) (z 0 + shift)))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_cubic_frozen_affine_expansion
  refine ⟨C, hC, ?_⟩
  intro p V out d c shift
  let coord : CubicReplicatedIndex → Fin 3 := fun j =>
    if j.1 = 0 then 1 else if j.2.val = 0 then 2 else 0
  let index : Fin 3 → CubicReplicatedIndex :=
    ![cubicRightReplica, ⟨0, ⟨0, by decide⟩⟩, cubicLeftReplica]
  have hindex (k : Fin 3) : coord (index k) = k := by fin_cases k <;> rfl
  let A : CubicReplicatedIndex → Fin 3 → ℤ := fun j k =>
    if coord j = d then 0 else if k = coord j then 1 else 0
  let b : CubicReplicatedIndex → ℤ := fun j =>
    (if coord j = d then c else 0) + (if coord j = 0 then shift else 0)
  obtain ⟨E⟩ := hfreeze V (index d) A b out (by intro k; simp [A, hindex])
  have hmap (x : Fin 3 → ℤ) (j : CubicReplicatedIndex) :
      integerAffineMap A b x j = (Function.update x d c) (coord j) +
        (if coord j = 0 then shift else 0) := by
    by_cases hj : coord j = d
    · simp [integerAffineMap, A, b, hj]
    · simp [integerAffineMap, A, b, hj, ite_mul]
      abel
  have heq (x : Fin 3 → ℤ) : integerAffineMap A b x =
      cubicTrilinearInput ((Function.update x d c) 1) ((Function.update x d c) 2)
        ((Function.update x d c) 0 + shift) := by
    funext j
    rw [hmap]
    by_cases hj : j.1 = 0
    · simp [coord, cubicTrilinearInput, hj]
    · by_cases hk : j.2.val = 0 <;> simp [coord, cubicTrilinearInput, hj, hk]
  exact ⟨by simpa only [heq] using E⟩

theorem exists_cubic_kernel_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (i j : Fin V.outputDim × Fin V.outputDim) (d : Fin 3) (c shift : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          V.cubicAntisymmetricPair i j (z 1) (z 2) (z 0 + shift))) := by
  obtain ⟨A, _, hscalar⟩ := exists_cubic_scalar_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Q + Polynomial.C B) ^ B + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p V i j d c shift
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let e : Fin 3 → Fin 3 := ![0, 2, 1]
  have he0 : e 0 = 0 := rfl
  have he1 : e 1 = 2 := rfl
  have he2 : e 2 = 1 := rfl
  have hswap (x : Fin 3 → ℤ) : Function.update (fun k => x (e k)) (e d) c =
      fun k => (Function.update x d c) (e k) := by
    funext k
    fin_cases d <;> fin_cases k <;> rfl
  have hright (out : Fin V.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
        (fun x => let z := Function.update x d c
          V.eval out (cubicTrilinearInput (z 2) (z 1) (z 0 + shift)))) := by
    obtain ⟨E⟩ := hscalar V out (e d) c shift
    have E' : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
        (fun x => let z := Function.update (fun k => x (e k)) (e d) c
          V.eval out (cubicTrilinearInput (z 1) (z 2) (z 0 + shift))) :=
      E.linearPullbackHom (fun k => ⟨⟨fun x => x (e k), rfl⟩, fun _ _ => rfl⟩)
    exact ⟨by simpa only [hswap, he0, he1, he2] using E'⟩
  obtain ⟨L₁⟩ := hscalar V i.1 d c shift
  obtain ⟨L₂⟩ := hscalar V i.2 d c shift
  obtain ⟨R₁⟩ := hright j.1
  obtain ⟨R₂⟩ := hright j.2
  obtain ⟨F₁⟩ := hmul hq L₁.conjugate R₁
  obtain ⟨F₂⟩ := hmul hq L₂.conjugate R₂
  obtain ⟨F⟩ := hmul (by positivity : 0 ≤ (q + B) ^ B) F₁ F₂
  have hcost : ((q + B) ^ B + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

theorem cubicAntisymmetricPair_norm {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (i j : Fin V.outputDim × Fin V.outputDim) (h y k : ℤ) :
    ‖V.cubicAntisymmetricPair i j h y k‖ ≤ 1 := by
  simp only [cubicAntisymmetricPair, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    ((mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval _ _)).trans
      (V.norm_eval _ _))).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval _ _)).trans (V.norm_eval _ _))

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
