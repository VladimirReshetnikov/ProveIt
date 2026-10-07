import GowersSzemeredi.Proofs16ParallelFaces

/-! Simultaneous pruning of all parallel coordinate faces, with one
ambient-volume deletion budget and a uniform prime threshold. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- All parallel l-dimensional faces can be regularized together. The
number of faces cancels their smaller volume in the deletion estimate. -/
theorem Theorem162At.restrict_parallel_faces {l : Nat} (hth : Theorem162At l)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N d r : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (e : Fin d ≃ Fin l ⊕ Fin r) (B : Finset (Point N d))
        (phi : Point N d → ZMod N), HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ z : Point N r,
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              ((splitCoordinateFace e z).domain B') ((splitCoordinateFace e z).pullback phi) := by
  classical
  obtain ⟨N0, hN0⟩ := hth.restrict_coordinate_face gamma theta hg hg1 ht ht1
  refine ⟨N0, ?_⟩
  intro N d r _ _ hN e B phi hprod
  choose C hCsub hCloss hCcover using
    (fun z : Point N r => hN0 N d hN B phi hprod (splitCoordinateFace e z))
  refine ⟨parallelFaceUnion e C, parallelFaceUnion_subset e B C hCsub, ?_, ?_⟩
  · have hdim : d = l + r := by
      simpa using Fintype.card_congr e
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun z (_ : z ∈ (Finset.univ : Finset (Point N r))) => hCloss z)
    have hBsum : (∑ z : Point N r, (((splitCoordinateFace e z).domain B).card : Real)) = B.card := by
      exact_mod_cast sum_coordinateFace_card e B
    have hCsum : (∑ z : Point N r, ((C z).card : Real)) = (parallelFaceUnion e C).card := by
      exact_mod_cast (parallelFaceUnion_card e C).symm
    rw [Finset.sum_sub_distrib, hBsum, hCsum] at hsum
    have hvol : (∑ _z : Point N r, theta * (N : Real) ^ l) = theta * (N : Real) ^ d := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card (Point N r) : Real) = (N : Real) ^ r := by
        simp [Point, ZMod.card]
      rw [hc, hdim, pow_add]
      ring
    rwa [hvol] at hsum
  · intro z
    rw [splitCoordinateFace_domain_union]
    exact hCcover z

end LeanProofs.GowersSzemeredi
