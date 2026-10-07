import GowersSzemeredi.Proofs16WeightedCollision

/-! Simultaneous weighted additive energy is collision energy of pair sums
in the graph. Its lower bound depends on the actual pair-sum support. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def section16ParallelPairSum {N p : Nat} (psi : Fin p → ZMod N → ZMod N)
    (z : ZMod N × ZMod N) : ZMod N × (Fin p → ZMod N) :=
  (z.1 + z.2, fun i => psi i z.1 + psi i z.2)

private def quadPairEquiv (X : Type*) : (Fin 4 → X) ≃ ((X × X) × (X × X)) where
  toFun q := ((q 0, q 1), (q 2, q 3))
  invFun z := ![z.1.1, z.1.2, z.2.1, z.2.2]
  left_inv q := by funext i; fin_cases i <;> rfl
  right_inv z := by rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl

private theorem sum_univ_indicator {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (f : X → Real) : (∑ x, if x ∈ S then f x else 0) = ∑ x ∈ S, f x := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

theorem weightedSimultaneousAdditiveEnergy_eq_collision {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (w : ZMod N → Real) (psi : Fin p → ZMod N → ZMod N) :
    weightedSimultaneousAdditiveEnergy E w psi =
      weightedCollisionEnergy ((E ×ˢ E)) (section16ParallelPairSum psi) (fun z => w z.1 * w z.2) := by
  classical
  unfold weightedSimultaneousAdditiveEnergy
  calc
    _ = ∑ z : (ZMod N × ZMod N) × (ZMod N × ZMod N),
      if z.1 ∈ (E ×ˢ E) then if z.2 ∈ (E ×ˢ E) then
        if section16ParallelPairSum psi z.1 = section16ParallelPairSum psi z.2 then
          (w z.1.1 * w z.1.2) * (w z.2.1 * w z.2.2) else 0 else 0 else 0 := by
      apply Fintype.sum_equiv (quadPairEquiv (ZMod N))
      intro q
      have hmem : (∀ t, q t ∈ E) ↔ (q 0, q 1) ∈ (E ×ˢ E) ∧ (q 2, q 3) ∈ (E ×ˢ E) := by
        simp only [Finset.mem_product]
        constructor
        · intro h
          exact ⟨⟨h 0, h 1⟩, h 2, h 3⟩
        · rintro ⟨⟨h0, h1⟩, h2, h3⟩ t
          fin_cases t <;> assumption
      have hadd : (IsAdditiveQuadruple q ∧ ∀ i, IsAdditiveQuadruple (fun t => psi i (q t))) ↔
          section16ParallelPairSum psi (q 0, q 1) = section16ParallelPairSum psi (q 2, q 3) := by
        simp only [IsAdditiveQuadruple, section16ParallelPairSum, Prod.mk.injEq, funext_iff]
      change (if (∀ t, q t ∈ E) ∧ IsAdditiveQuadruple q ∧
        (∀ i, IsAdditiveQuadruple (fun t => psi i (q t))) then ∏ t, w (q t) else 0) = _
      simp only [hmem, hadd, quadPairEquiv, Equiv.coe_fn_mk, Fin.prod_univ_four, ite_and]
      split_ifs <;> ring
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp only [sum_univ_indicator, weightedCollisionEnergy]

/-- A support of at most M graph-pair sums gives the fourth-moment lower
bound. No positivity assumption on the weights is required. -/
theorem weightedSimultaneousAdditiveEnergy_support_bound {N p : Nat} [NeZero N]
    (E : Finset (ZMod N)) (w : ZMod N → Real) (psi : Fin p → ZMod N → ZMod N)
    (T : Finset (ZMod N × (Fin p → ZMod N))) {M : Real}
    (hmap : ∀ a ∈ E, ∀ b ∈ E, section16ParallelPairSum psi (a, b) ∈ T)
    (hcard : (T.card : Real) ≤ M) :
    (∑ x ∈ E, w x) ^ 4 ≤ M * weightedSimultaneousAdditiveEnergy E w psi := by
  have h := weightedCollisionEnergy_mass_bound ((E ×ˢ E)) T (section16ParallelPairSum psi)
    (fun z => w z.1 * w z.2) (fun z hz => hmap _ (Finset.mem_product.mp hz).1 _ (Finset.mem_product.mp hz).2)
  have hsum : (∑ z ∈ (E ×ˢ E), w z.1 * w z.2) = (∑ x ∈ E, w x) ^ 2 := by
    rw [Finset.sum_product, ← Finset.sum_mul_sum, pow_two]
  rw [hsum, ← weightedSimultaneousAdditiveEnergy_eq_collision] at h
  have hnonneg := weightedCollisionEnergy_nonneg ((E ×ˢ E)) (section16ParallelPairSum psi)
    (fun z => w z.1 * w z.2)
  rw [← weightedSimultaneousAdditiveEnergy_eq_collision] at hnonneg
  apply le_trans ?_ (mul_le_mul_of_nonneg_right hcard hnonneg)
  simpa only [← pow_mul] using h

end LeanProofs.GowersSzemeredi
