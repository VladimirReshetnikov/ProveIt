import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Sections17_18

/-! Removing a polynomial phase that varies between partition cells.
The degree and error tolerance are common; the coefficients need not be. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Cell-dependent polynomial phases can be removed without changing the
global cell-count exponent of Lemma 5.14. The function may be complex-valued. -/
theorem variable_polynomial_phase_refinement {N M k : Nat} [NeZero N]
    (Q : Fin M → ModAP N) (phi : Fin M → ZMod N → ZMod N)
    (f : ZMod N → Complex) (alpha : Real)
    (hk : 1 ≤ k) (hα : 0 < alpha)
    (hphi : ∀ i, PolynomialOn k Finset.univ (phi i)) (hf : DiscValued f)
    (hQ : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hphase : alpha * N ≤ ∑ i, ‖∑ s ∈ (Q i).carrier, f s * exponential (-(phi i s))‖) :
    ∃ L : Nat, ∃ R : Fin L → ModAP N,
      IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
      IsRefinement (fun j ↦ (R j).carrier) (fun i ↦ (Q i).carrier) ∧
      (∀ j, (R j).IsProper) ∧
      (L : Real) ≤ section5LocalRefinementConstant k alpha *
        (M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
        (N : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) ∧
      (alpha / 2) * N ≤ ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
  classical
  have hM : 0 < M := by
    obtain ⟨i, _⟩ := (hQ.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact Nat.zero_lt_of_lt i.isLt
  have hcards : ∑ i, (Q i).carrier.card = N := by
    simpa only [Finset.card_univ, ZMod.card] using hQ.sum_card
  choose L R hpart hproper hcount herror using fun i : Fin M ↦
    section5_efficient_local_phase_refinement_arbitrary_of_corollary_5_6
      corollary_5_6_holds (Q i) (phi i) alpha hk (hphi i) hα
  refine ⟨∑ i, L i, section5Flatten L R,
    section5Flatten_partition Q L R hQ hpart,
    section5Flatten_refinement Q L R hQ hpart,
    section5Flatten_isProper L R hproper, ?_, ?_⟩
  · have hK : 0 < polynomialPartitionConstant k := by unfold polynomialPartitionConstant; positivity
    have hjensen := section5_sum_rpow_le hM hK (fun i ↦ (Q i).carrier.card) hcards
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ i, section5LocalRefinementConstant k alpha *
          ((Q i).carrier.card : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) :=
        Finset.sum_le_sum fun i _ ↦ hcount i
      _ = section5LocalRefinementConstant k alpha *
          ∑ i, ((Q i).carrier.card : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ section5LocalRefinementConstant k alpha *
          ((M : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ *
            (N : Real) ^ (1 - (polynomialPartitionConstant k : Real)⁻¹)) :=
        mul_le_mul_of_nonneg_left hjensen (section5LocalRefinementConstant_pos k alpha).le
      _ = _ := by ring
  · have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) ↦ herror i f hf)
    have hcardsR : ∑ i, ((Q i).carrier.card : Real) = N := by exact_mod_cast hcards
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcardsR] at hsum
    rw [section5Flatten_sum L R (fun P ↦ ‖∑ s ∈ P.carrier, f s‖)]
    linarith only [hphase, hsum]

/-- Adding a linear polynomial preserves every positive degree bound. -/
theorem PolynomialOn.add_linear {N k : Nat} {S : Finset (ZMod N)}
    {phi : ZMod N → ZMod N} (hphi : PolynomialOn k S phi) (hk : 1 ≤ k) (r : ZMod N) :
    PolynomialOn k S (fun x ↦ phi x + r * x) := by
  classical
  obtain ⟨c, hc⟩ := hphi
  let j : Fin (k + 1) := ⟨1, by omega⟩
  refine ⟨fun i ↦ c i + if i = j then r else 0, fun x hx ↦ ?_⟩
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [← hc x hx, Finset.sum_ite_eq']
  simp [j]

/-- Successive twists combine by adding their polynomial phases. -/
theorem phaseTwist_mul_linear {N : Nat} [NeZero N] (f : ZMod N → Complex)
    (phi : ZMod N → ZMod N) (r x : ZMod N) :
    phaseTwist f phi x * exponential (-(r * x)) =
      f x * exponential (-(phi x + r * x)) := by
  simp only [phaseTwist, neg_add, exponential, AddChar.map_add_eq_mul]
  ring

end LeanProofs.GowersSzemeredi
