import GowersSzemeredi.Proofs16IndependentFamilyIncrement
import GowersSzemeredi.Proofs16SmallCoverIndices

/-! Uniform bounds on the total cardinality of independent frequency
families provide a finite budget for dense simultaneous enlargements. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem independent_family_total_card_bound {N : Nat} [NeZero N] {I : Type*}
    (D K : I → Finset (ZMod N)) (Omega : Finset I) (k R : Nat)
    (hD : ∀ i ∈ Omega, AddDissociated (D i : Set (ZMod N)))
    (hDK : ∀ i ∈ Omega, D i ⊆ boundedFrequencySpan (fun b : K i => (b : ZMod N)) R)
    (hK : ∀ i ∈ Omega, (K i).card ≤ k) :
    (∑ i ∈ Omega, (D i).card) ≤ Omega.card*spanGeneratorBound k R := by
  calc (∑ i ∈ Omega, (D i).card) ≤ ∑ _i ∈ Omega, spanGeneratorBound k R := by
         apply Finset.sum_le_sum
         intro i hi
         exact (subsetSum_count_rank_bound _ _ _
           (dissociated_boundedSpan_count (K i) (D i) R (hDK i hi) (hD i hi))).trans
           (spanGeneratorBound_mono_rank (hK i hi) R)
    _ = _ := by simp

/-- A sequence of positive-density enlargements cannot exceed the
uniform per-index rank budget divided by its gain per step. -/
theorem independent_family_iteration_budget {N : Nat} [NeZero N] {I : Type*}
    (D : Nat → I → Finset (ZMod N)) (K : I → Finset (ZMod N))
    (Omega : Finset I) (k R n : Nat) {eta : Real}
    (hOmega : Omega.Nonempty)
    (hD : ∀ i ∈ Omega, AddDissociated (D n i : Set (ZMod N)))
    (hDK : ∀ i ∈ Omega, D n i ⊆ boundedFrequencySpan (fun b : K i => (b : ZMod N)) R)
    (hK : ∀ i ∈ Omega, (K i).card ≤ k)
    (hstep : ∀ j < n, (∑ i ∈ Omega, ((D j i).card : Real))+eta*Omega.card ≤
      ∑ i ∈ Omega, ((D (j+1) i).card : Real)) :
    (n : Real)*eta ≤ spanGeneratorBound k R := by
  have hiter : ∀ m ≤ n, (m : Real)*eta*Omega.card ≤ ∑ i ∈ Omega, ((D m i).card : Real) := by
    intro m
    induction m with
    | zero => intro _; simp only [Nat.cast_zero,zero_mul]; positivity
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hnext := hstep m (by omega)
      push_cast
      nlinarith only [hprev,hnext]
  have hbudget : (∑ i ∈ Omega, ((D n i).card : Real)) ≤
      (Omega.card : Real)*spanGeneratorBound k R := by
    exact_mod_cast independent_family_total_card_bound (D n) K Omega k R hD hDK hK
  have hpos : (0 : Real) < Omega.card := by exact_mod_cast Finset.card_pos.mpr hOmega
  apply le_of_mul_le_mul_right (a := (Omega.card : Real)) _ hpos
  simpa only [mul_comm (Omega.card : Real)] using (hiter n le_rfl).trans hbudget

end LeanProofs.GowersSzemeredi
