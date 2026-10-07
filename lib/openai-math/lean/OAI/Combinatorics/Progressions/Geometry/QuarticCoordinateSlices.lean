import OAI.Combinatorics.Progressions.Estimates.QuarticAntisymmetricTransfer

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_quartic_frozen_affine_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (d : QuarticReplicatedIndex) (A : QuarticReplicatedIndex → Fin 4 → ℤ)
      (b : QuarticReplicatedIndex → ℤ) (out : Fin W.outputDim),
      (∀ k, A d k = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        (fun x => W.eval out (integerAffineMap A b x))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest (fun _ : QuarticReplicatedIndex => 1)
  refine ⟨C, hC, ?_⟩
  intro p W d A b out hA
  classical
  let S : Finset QuarticReplicatedIndex := Finset.univ.erase d
  have hcard : Fintype.card QuarticReplicatedIndex = 4 := by
    calc
      _ = ∑ j : Fin 2, mixedCorrelationDegree 3 j := replicatedIndex_card _
      _ = 4 := by rw [Fin.sum_univ_two]; rfl
  have hdegree : (∑ j ∈ S, (1 : ℕ)) = 3 := by simp [S, hcard]
  obtain ⟨t, n, ht, _hn, D, hD⟩ := hfreeze W S b out
  have ht3 : t = 3 := ht.trans hdegree
  rcases ht3 with rfl
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _hTnorm, hT, _hzero, heval⟩ := hD
  let U := T.affinePullback (fun j k => A j.val k) (fun j => b j.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hvalue (x : Fin 4 → ℤ) : U.eval x = W.eval out (integerAffineMap A b x) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    apply congrArg (W.eval out)
    funext j
    by_cases hj : j ∈ S
    · simp [freezeCoordinates, hj, integerAffineMap]
    · have hjd : j = d := by simpa [S] using hj
      subst j
      simp [freezeCoordinates, hj, integerAffineMap, hA]
  let E : NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C) U.eval :=
    NativeIntegerExpansion.ofTest U hU (fun _ => rfl)
  have heq : U.eval = (fun x => W.eval out (integerAffineMap A b x)) := funext hvalue
  exact ⟨heq ▸ E⟩

theorem exists_quartic_scalar_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (out : Fin W.outputDim) (d : Fin 4) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          W.eval out (quarticInput (z 0) ![z 1, z 2, z 3]))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_quartic_frozen_affine_expansion
  refine ⟨C, hC, ?_⟩
  intro p W out d c
  let coord : QuarticReplicatedIndex → Fin 4 := fun j =>
    if j.1 = 0 then 0 else if j.2.val = 0 then 1 else if j.2.val = 1 then 2 else 3
  let index : Fin 4 → QuarticReplicatedIndex :=
    ![⟨0, ⟨0, by decide⟩⟩, quarticReplica 0, quarticReplica 1, quarticReplica 2]
  have hindex (k : Fin 4) : coord (index k) = k := by fin_cases k <;> rfl
  let A : QuarticReplicatedIndex → Fin 4 → ℤ := fun j k =>
    if coord j = d then 0 else if k = coord j then 1 else 0
  let b : QuarticReplicatedIndex → ℤ := fun j => if coord j = d then c else 0
  obtain ⟨E⟩ := hfreeze W (index d) A b out (by intro k; simp [A, hindex])
  have hmap (x : Fin 4 → ℤ) (j : QuarticReplicatedIndex) :
      integerAffineMap A b x j = (Function.update x d c) (coord j) := by
    by_cases hj : coord j = d <;> simp [integerAffineMap, A, b, hj, ite_mul]
  have heq (x : Fin 4 → ℤ) : integerAffineMap A b x =
      quarticInput ((Function.update x d c) 0)
        ![(Function.update x d c) 1, (Function.update x d c) 2,
          (Function.update x d c) 3] := by
    funext j
    rw [hmap]
    by_cases hj : j.1 = 0
    · simp [coord, quarticInput, hj]
    · by_cases hk : j.2.val = 0
      · simp [coord, quarticInput, hj, hk]
      · by_cases hl : j.2.val = 1 <;> simp [coord, quarticInput, hj, hk, hl]
  exact ⟨by simpa only [heq] using E⟩

theorem exists_quartic_kernel_coordinate_slice :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (i j : Fin W.outputDim) (d : Fin 4) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        (fun x => W.quarticAntisymmetric i j (Function.update x d c))) := by
  obtain ⟨A, _, hscalar⟩ := exists_quartic_scalar_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let e : Fin 4 → Fin 4 := ![1, 0, 2, 3]
  have he0 : e 0 = 1 := rfl
  have he1 : e 1 = 0 := rfl
  have he2 : e 2 = 2 := rfl
  have he3 : e 3 = 3 := rfl
  have hswap (x : Fin 4 → ℤ) : Function.update (fun k => x (e k)) (e d) c =
      fun k => (Function.update x d c) (e k) := by
    funext k
    fin_cases d <;> fin_cases k <;> rfl
  obtain ⟨L⟩ := hscalar W i d c
  obtain ⟨R⟩ := hscalar W j (e d) c
  have R' : NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 q
      (fun x => let z := Function.update x d c
        W.eval j (quarticInput (z 1) ![z 0, z 2, z 3])) := by
    have E : NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 q
        (fun x => let z := Function.update (fun k => x (e k)) (e d) c
          W.eval j (quarticInput (z 0) ![z 1, z 2, z 3])) :=
      R.linearPullbackHom (fun k => ⟨⟨fun x => x (e k), rfl⟩, fun _ _ => rfl⟩)
    simpa only [hswap, he0, he1, he2, he3] using E
  obtain ⟨F⟩ := hmul hq L R'.conjugate
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
