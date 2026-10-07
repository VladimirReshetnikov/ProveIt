import GowersSzemeredi.Proofs16ParallelFaceInduction

/-! Successive coordinate-direction restrictions preserve previous covers
and add their deletion budgets. The thresholds remain uniform in the grid. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A finite family of downward-closed conclusions can be obtained by
successive restrictions, with the sum of their individual deletion costs. -/
theorem HasProductProperty.restrict_finite_family {N d : Nat} [NeZero N]
    {I : Type*} (s : Finset I) (P : I → Finset (Point N d) → Prop)
    (cost : I → Real) {gamma : Real} {phi : Point N d → ZMod N}
    (hmono : ∀ i, ∀ B C, C ⊆ B → P i B → P i C)
    (hstep : ∀ i ∈ s, ∀ B, HasProductProperty B phi gamma →
      ∃ C, C ⊆ B ∧ (B.card : Real) - cost i ≤ C.card ∧ P i C)
    {B : Finset (Point N d)} (hprod : HasProductProperty B phi gamma) :
    ∃ C, C ⊆ B ∧ (B.card : Real) - ∑ i ∈ s, cost i ≤ C.card ∧ ∀ i ∈ s, P i C := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨B, le_rfl, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hCB, hCcard, hC⟩ := ih (fun j hj => hstep j (Finset.mem_insert_of_mem hj))
    obtain ⟨D, hDC, hDcard, hD⟩ := hstep i (Finset.mem_insert_self i s) C (hprod.mono hCB)
    refine ⟨D, hDC.trans hCB, ?_, ?_⟩
    · rw [Finset.sum_insert hi]
      linarith
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact hD
      · exact hmono j C D hDC (hC j hjs)

/-- Apply the induction hypotheses to finitely many coordinate directions,
possibly of different dimensions. Each direction retains its original
dimension-dependent cover parameter. -/
theorem restrict_finite_parallel_directions {I : Type*} [Fintype I]
    (d : Nat) (l r : I → Nat) (e : ∀ i, Fin d ≃ Fin (l i) ⊕ Fin (r i))
    (hth : ∀ i, Theorem162At (l i)) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - (Fintype.card I : Real) * theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ (i : I) (z : Point N (r i)),
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma (l i))
              ((splitCoordinateFace (e i) z).domain B')
              ((splitCoordinateFace (e i) z).pullback phi) := by
  classical
  choose T hT using (fun i => (hth i).restrict_parallel_faces gamma theta hg hg1 ht ht1)
  refine ⟨∑ i, T i, ?_⟩
  intro N _ _ hN B phi hprod
  let P := fun i (C : Finset (Point N d)) => ∀ z : Point N (r i),
    MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma (l i))
      ((splitCoordinateFace (e i) z).domain C) ((splitCoordinateFace (e i) z).pullback phi)
  have hmono : ∀ i, ∀ C D, D ⊆ C → P i C → P i D := by
    intro i C D hDC hC z
    exact (hC z).mono ((splitCoordinateFace (e i) z).domain_mono hDC)
  have hstep : ∀ i ∈ (Finset.univ : Finset I), ∀ C, HasProductProperty C phi gamma →
      ∃ D, D ⊆ C ∧ (C.card : Real) - theta * (N : Real) ^ d ≤ D.card ∧ P i D := by
    intro i _ C hC
    have hi : T i ≤ N := (Finset.single_le_sum (fun j _ => Nat.zero_le (T j))
      (Finset.mem_univ i)).trans hN
    exact hT i N d (r i) hi (e i) C phi hC
  obtain ⟨C, hCB, hcard, hC⟩ := hprod.restrict_finite_family Finset.univ P
    (fun _ => theta * (N : Real) ^ d) hmono hstep
  refine ⟨C, hCB, ?_, fun i => hC i (Finset.mem_univ i)⟩
  simpa [mul_assoc] using hcard

end LeanProofs.GowersSzemeredi
