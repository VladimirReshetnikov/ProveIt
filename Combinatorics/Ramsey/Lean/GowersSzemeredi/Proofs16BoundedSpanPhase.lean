import GowersSzemeredi.Proofs16SmallSpanGenerators

/-! Phase control extends from generators to their bounded span, with an
explicit loss equal to the number of generators times the coefficient cap. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem centeredAbs_mul_le {N : Nat} [NeZero N] (a b : ZMod N) :
    centeredAbs (a * b) ≤ centeredAbs a * centeredAbs b := by
  have heq : (((a.valMinAbs * b.valMinAbs) : Int) : ZMod N) = a * b := by push_cast; rfl
  calc centeredAbs (a * b) ≤ (a.valMinAbs * b.valMinAbs).natAbs := by
        rw [← heq]
        exact recurrence_centeredAbs_intCast_le _
    _ = centeredAbs a * centeredAbs b := by rw [Int.natAbs_mul]; rfl

theorem centeredAbs_sum_le_sum {N : Nat} [NeZero N] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod N) :
    centeredAbs (∑ i ∈ s, f i) ≤ ∑ i ∈ s, centeredAbs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [centeredAbs]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (centeredAbs_add_le _ _).trans (Nat.add_le_add (Nat.le_refl _) ih)

theorem boundedFrequencySpan_phase_bound {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (gamma : ι → ZMod N) (R : Nat) (x : ZMod N) {rho : Real}
    (hgamma : ∀ i, (centeredAbs (gamma i * x) : Real) ≤ rho * N)
    {q : ZMod N} (hq : q ∈ boundedFrequencySpan gamma R) :
    (centeredAbs (q * x) : Real) ≤ Fintype.card ι * (R : Real) * rho * N := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  rw [Finset.sum_mul]
  calc (centeredAbs (∑ i, (v i : ZMod N) * gamma i * x) : Real)
      ≤ ∑ i, (centeredAbs ((v i : ZMod N) * gamma i * x) : Real) := by
        exact_mod_cast centeredAbs_sum_le_sum Finset.univ (fun i => (v i : ZMod N) * gamma i * x)
    _ ≤ ∑ _i : ι, (R : Real) * (rho * N) := by
      apply Finset.sum_le_sum
      intro i hi
      have hmul : (centeredAbs ((v i : ZMod N) * (gamma i * x)) : Real) ≤
          (centeredAbs (v i : ZMod N) : Real) * centeredAbs (gamma i * x) := by
        exact_mod_cast centeredAbs_mul_le (v i : ZMod N) (gamma i * x)
      have hc : (centeredAbs (v i : ZMod N) : Real) ≤ R := by
        exact_mod_cast (Finset.mem_filter.mp (v i).property).2
      rw [mul_assoc]
      exact hmul.trans (mul_le_mul hc (hgamma i) (by positivity) (by positivity))
    _ = Fintype.card ι * (R : Real) * rho * N := by simp; ring

/-- A Bohr condition on generators controls the entire bounded span. -/
theorem bohr_subset_boundedFrequencySpan_bohr {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (R : Nat) (rho : Real) :
    bohr K rho ⊆ bohr (boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
      ((K.card : Real) * R * rho) := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
  simpa only [Fintype.card_coe] using boundedFrequencySpan_phase_bound
    (fun k : K => (k : ZMod N)) R x (fun k => (Finset.mem_filter.mp hx).2 k k.property) hq

end LeanProofs.GowersSzemeredi
