import GowersSzemeredi.Proofs16PrimeColumnIdentities
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Cardinality bounds for a family of column Bohr neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem columnBohrDomain_card {N : Nat} [NeZero N] (P : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (s : Real) :
    (columnBohrDomain P T s).card = ∑ x ∈ P, (bohr (T x) s).card := by
  have he : columnBohrDomain P T s = P.biUnion (fun x => {x} ×ˢ bohr (T x) s) := by
    ext ⟨x,y⟩
    simp [columnBohrDomain]
  rw [he,Finset.card_biUnion]
  · simp
  · intro x hx y hy hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact hne ((Finset.mem_singleton.mp (Finset.mem_product.mp hp).1).symm.trans
      (Finset.mem_singleton.mp (Finset.mem_product.mp hq).1))

/-- A uniform rank bound yields an ambient lower bound for the whole
column domain, with no regularity assumption. -/
theorem columnBohrDomain_card_lower {N D Q : Nat} [NeZero N] [NeZero Q]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) {s : Real}
    (hQ : 1 ≤ s*Q) (hT : ∀ x ∈ P, (T x).card ≤ D) :
    P.card*N ≤ Q^D*(columnBohrDomain P T s).card := by
  rw [columnBohrDomain_card,Finset.mul_sum]
  calc P.card*N = ∑ _x ∈ P, N := by simp
    _ ≤ ∑ x ∈ P, Q^D*(bohr (T x) s).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact (bohr_card_lower (T x) Q hQ).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (NeZero.pos Q) (hT x hx)))

/-- The ambient density estimate, in a form avoiding division. -/
theorem columnBohrDomain_density_lower {N D Q : Nat} [NeZero N] [NeZero Q]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N)) {s delta : Real}
    (hQ : 1 ≤ s*Q) (hT : ∀ x ∈ P, (T x).card ≤ D)
    (hP : delta*N ≤ (P.card : Real)) :
    delta*(N : Real)^2 ≤ (Q : Real)^D*(columnBohrDomain P T s).card := by
  have hc : (P.card : Real)*N ≤ (Q : Real)^D*(columnBohrDomain P T s).card := by
    exact_mod_cast columnBohrDomain_card_lower P T hQ hT
  have hm := mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg N : (0 : Real) ≤ N)
  nlinarith only [hc,hm]

end LeanProofs.GowersSzemeredi
