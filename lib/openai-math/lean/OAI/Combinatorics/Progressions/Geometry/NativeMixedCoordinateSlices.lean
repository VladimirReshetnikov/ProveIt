/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.NativeMixedReflectionBridge

namespace OAI

section

namespace Erdos3

def mixedInputCoordinate (n : ℕ) : MixedReplicatedIndex (n + 1) → Fin (n + 2) :=
  mixedSlotInput 0 1 (fun j => j.succ.succ)

def mixedCoordinateIndex (n : ℕ) : Fin (n + 2) → MixedReplicatedIndex (n + 1) :=
  Fin.cases (mixedHead (n + 1)) (fun j => mixedReplica j)

theorem mixedInputCoordinate_index (n : ℕ) (k : Fin (n + 2)) :
    mixedInputCoordinate n (mixedCoordinateIndex n k) = k := by
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedInputCoordinate_eval (n : ℕ) {α : Type*} (x : Fin (n + 2) → α) :
    (fun j => x (mixedInputCoordinate n j)) =
      mixedSlotInput (x 0) (x 1) (fun j => x j.succ.succ) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨k, rfl⟩
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedExchangeCoordinate_involutive (n : ℕ) :
    Function.Involutive (mixedExchangeCoordinate n) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k <;> rfl

theorem mixedExchangeCoordinate_update (n : ℕ) {α : Type*}
    (x : Fin (n + 2) → α) (d : Fin (n + 2)) (c : α) :
    Function.update (fun k => x (mixedExchangeCoordinate n k)) (mixedExchangeCoordinate n d) c =
      fun k => (Function.update x d c) (mixedExchangeCoordinate n k) := by
  funext k
  have hi (k : Fin (n + 2)) :
      mixedExchangeCoordinate n (mixedExchangeCoordinate n k) = k :=
    mixedExchangeCoordinate_involutive n k
  by_cases h : k = mixedExchangeCoordinate n d
  · subst k
    simp only [Function.update_self, hi]
  · have hk : mixedExchangeCoordinate n k ≠ d := by
      intro heq
      apply h
      have h' := congrArg (mixedExchangeCoordinate n) heq
      simpa only [hi] using h'
    simp only [Function.update_of_ne h, Function.update_of_ne hk]

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open Module
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_mixed_frozen_affine_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : (MixedReplicatedIndex (n + 1)) => 1) p)
      (d : (MixedReplicatedIndex (n + 1))) (A : (MixedReplicatedIndex (n + 1)) → Fin (n + 2) → ℤ)
      (b : (MixedReplicatedIndex (n + 1)) → ℤ) (out : Fin W.outputDim),
      (∀ k, A d k = 0) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.eval out (integerAffineMap A b x))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_freezing_niltest (fun _ : (MixedReplicatedIndex (n + 1)) => 1)
  refine ⟨C, hC, ?_⟩
  intro p W d A b out hA
  classical
  let S : Finset (MixedReplicatedIndex (n + 1)) := Finset.univ.erase d
  have hcard : Fintype.card (MixedReplicatedIndex (n + 1)) = n + 2 :=
    replicatedMixed_card (n + 1)
  have hdegree : (∑ j ∈ S, (1 : ℕ)) = n + 1 := by simp [S, hcard]
  obtain ⟨t, dim, ht, _hdim, D, hD⟩ := hfreeze W S b out
  have ht3 : t = n + 1 := ht.trans hdegree
  rcases ht3 with rfl
  let K := W.multi.filtration.weightedSubalgebra (retainedCoordinateWeight S)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 D.basis
  obtain ⟨T, _hTnorm, hT, _hzero, heval⟩ := hD
  let U := T.affinePullback (fun j k => A j.val k) (fun j => b j.val)
  have hU : U.ComplexityLE ((p + C) ^ C) := hT
  have hvalue (x : Fin (n + 2) → ℤ) : U.eval x = W.eval out (integerAffineMap A b x) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_affinePullback, heval]
    apply congrArg (W.eval out)
    funext j
    by_cases hj : j ∈ S
    · simp [freezeCoordinates, hj, integerAffineMap]
    · have hjd : j = d := by simpa [S] using hj
      subst j
      simp [freezeCoordinates, hj, integerAffineMap, hA]
  let E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C) U.eval :=
    NativeIntegerExpansion.ofTest U hU (fun _ => rfl)
  have heq : U.eval = (fun x => W.eval out (integerAffineMap A b x)) := funext hvalue
  exact ⟨heq ▸ E⟩

theorem exists_mixed_scalar_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (out : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => let z := Function.update x d c
          W.eval out (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ)))) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_mixed_frozen_affine_expansion n
  refine ⟨C, hC, ?_⟩
  intro p W out d c
  let coord := mixedInputCoordinate n
  let index := mixedCoordinateIndex n
  have hindex (k : Fin (n + 2)) : coord (index k) = k := mixedInputCoordinate_index n k
  let A : MixedReplicatedIndex (n + 1) → Fin (n + 2) → ℤ := fun j k =>
    if coord j = d then 0 else if k = coord j then 1 else 0
  let b : MixedReplicatedIndex (n + 1) → ℤ := fun j => if coord j = d then c else 0
  obtain ⟨E⟩ := hfreeze W (index d) A b out (by intro k; simp [A, hindex])
  have hmap (x : Fin (n + 2) → ℤ) (j : MixedReplicatedIndex (n + 1)) :
      integerAffineMap A b x j = (Function.update x d c) (coord j) := by
    by_cases hj : coord j = d <;> simp [integerAffineMap, A, b, hj, ite_mul]
  have heq (x : Fin (n + 2) → ℤ) : integerAffineMap A b x =
      mixedSlotInput ((Function.update x d c) 0) ((Function.update x d c) 1)
        (fun l => (Function.update x d c) l.succ.succ) := by
    funext j
    rw [hmap]
    exact congrFun (mixedInputCoordinate_eval n (Function.update x d c)) j
  exact ⟨by simpa only [heq] using E⟩

theorem exists_mixed_kernel_coordinate_slice (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (d : Fin (n + 2)) (c : ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (Function.update x d c))) := by
  obtain ⟨A, _, hscalar⟩ := exists_mixed_scalar_coordinate_slice n
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j d c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let e := mixedExchangeCoordinate n
  have he0 : e 0 = 1 := rfl
  have he1 : e 1 = 0 := rfl
  have hetail (l : Fin n) : e l.succ.succ = l.succ.succ := rfl
  have hswap (x : Fin (n + 2) → ℤ) : Function.update (fun k => x (e k)) (e d) c =
      fun k => (Function.update x d c) (e k) := mixedExchangeCoordinate_update n x d c
  obtain ⟨L⟩ := hscalar W i d c
  obtain ⟨R⟩ := hscalar W j (e d) c
  have R' : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
      (fun x => let z := Function.update x d c
        W.eval j (mixedSlotInput (z 1) (z 0) (fun l => z l.succ.succ))) := by
    have E : NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q
        (fun x => let z := Function.update (fun k => x (e k)) (e d) c
          W.eval j (mixedSlotInput (z 0) (z 1) (fun l => z l.succ.succ))) :=
      R.linearPullbackHom (fun k => ⟨⟨fun x => x (e k), rfl⟩, fun _ _ => rfl⟩)
    simpa only [hswap, he0, he1, hetail] using E
  obtain ⟨F⟩ := hmul hq L R'.conjugate
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨F.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
