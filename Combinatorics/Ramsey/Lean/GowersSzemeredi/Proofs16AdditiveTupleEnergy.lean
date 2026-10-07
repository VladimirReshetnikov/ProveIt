import GowersSzemeredi.Proofs16WeightedCollision

/-! The source additive-tuple count is a collision energy of half-tuple
sums. Cauchy--Schwarz gives its density lower bound in every order. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private def tuplePairEquiv (d : Nat) (G : Type*) :
    ((Fin d → G) × (Fin d → G)) ≃ (Fin (2 * d) → G) :=
  (Fin.appendEquiv d d).trans
    ((finCongr (Nat.two_mul d).symm).arrowCongr (Equiv.refl G))

private theorem tuplePair_additive {G : Type*} [AddCommMonoid G]
    (d : Nat) (a b : Fin d → G) :
    IsAdditiveTuple (tuplePairEquiv d G (a, b)) ↔ (∑ i, a i) = ∑ i, b i := by
  classical
  unfold IsAdditiveTuple
  simp only [Finset.sum_filter]
  rw [← (finCongr (Nat.two_mul d).symm).sum_comp,
    ← (finCongr (Nat.two_mul d).symm).sum_comp]
  have hsmall (i : Fin d) : ¬ d ≤ i.val := Nat.not_le_of_gt i.isLt
  simp [tuplePairEquiv, Fin.sum_univ_add, Fin.is_lt, hsmall, -Fin.natAdd_eq_addNat]

private theorem tuplePair_mem {G : Type*} (d : Nat) (A : Finset G)
    (a b : Fin d → G) :
    (∀ i, tuplePairEquiv d G (a, b) i ∈ A) ↔ (∀ i, a i ∈ A) ∧ ∀ i, b i ∈ A := by
  rw [← (finCongr (Nat.two_mul d).symm).forall_congr_right]
  simp [tuplePairEquiv, Fin.forall_fin_add, -Fin.natAdd_eq_addNat]

theorem additiveTupleCount_eq_collision {G : Type*} [Fintype G]
    [DecidableEq G] [AddCommMonoid G] (d : Nat) (A : Finset G) :
    (additiveTupleCount d A : Real) =
      weightedCollisionEnergy (Fintype.piFinset (fun _ : Fin d => A))
        (fun a => ∑ i, a i) (fun _ => 1) := by
  classical
  let T := Fintype.piFinset (fun _ : Fin d => A)
  have hc : additiveTupleCount d A =
      ((T ×ˢ T).filter fun p => (∑ i, p.1 i) = ∑ i, p.2 i).card := by
    unfold additiveTupleCount countWhere
    symm
    apply Finset.card_equiv (tuplePairEquiv d G)
    rintro ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      tuplePair_mem, tuplePair_additive, T, Fintype.mem_piFinset]
  rw [hc]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.sum_product,
    weightedCollisionEnergy, one_mul]
  dsimp only [T]

theorem additiveTupleCount_mass_bound {G : Type*} [Fintype G]
    [DecidableEq G] [AddCommMonoid G] (d : Nat) (A : Finset G) :
    (A.card : Real) ^ (2 * d) ≤ (Fintype.card G : Real) * additiveTupleCount d A := by
  classical
  have h := weightedCollisionEnergy_mass_bound
    (Fintype.piFinset (fun _ : Fin d => A)) Finset.univ
    (fun a => ∑ i, a i) (fun _ => (1 : Real)) (fun _ _ => Finset.mem_univ _)
  rw [← additiveTupleCount_eq_collision] at h
  simpa [Fintype.card_piFinset, ← pow_mul, Nat.mul_comm] using h

end LeanProofs.GowersSzemeredi
