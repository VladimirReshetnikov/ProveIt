import GowersSzemeredi.Proofs05VarianceIncrement
import GowersSzemeredi.ProofInfrastructure

/-! Exact balanced mass on a cover of a set. These estimates supply the
parent-size lower bounds in the high-correlation branch of Corollary 5.8.
They use the mass of the balanced function, rather than a unit bound at
each point, so the estimates retain the factor `1 - density A`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem IsPartition.sum_values {X R : Type*} [DecidableEq X] [AddCommMonoid R]
    {m : Nat} {P : Fin m → Finset X} {U : Finset X}
    (hP : IsPartition P U) (f : X → R) :
    (∑ i, ∑ x ∈ P i, f x) = ∑ x ∈ U, f x := by
  classical
  have hdis : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hP.2 i j (bne_iff_ne.mpr hij)
  have hU : Finset.univ.biUnion P = U := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hP.1 x).symm
  rw [← hU, Finset.sum_biUnion hdis]

theorem balanced_eq_realSetBalanced {N : Nat} (A : Finset (ZMod N)) (x : ZMod N) :
    balanced A x = (realSetBalanced A x : Complex) := by
  classical
  simp only [balanced, indicator, realSetBalanced, realSetIndicator]
  split_ifs <;> push_cast <;> rfl

theorem norm_balanced_indicator_formula {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (x : ZMod N) :
    ‖balanced A x‖ = (1 - 2 * density A) * realSetIndicator A x + density A := by
  classical
  rw [balanced_eq_realSetBalanced, Complex.norm_real, Real.norm_eq_abs]
  have hd := density_nonneg A
  have hd1 := density_le_one A
  dsimp [realSetBalanced, realSetIndicator]
  split_ifs
  · rw [abs_of_nonneg (by linarith)]
    ring
  · rw [abs_of_nonpos (by linarith)]
    ring

theorem sum_norm_balanced_on_cover {N : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (hAU : A ⊆ U) :
    (∑ x ∈ U, ‖balanced A x‖) =
      density A * ((N : Real) + U.card - 2 * density A * N) := by
  have hcard : (A.card : Real) = density A * N := by
    exact (div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)).symm
  simp only [norm_balanced_indicator_formula, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_realSetIndicator_on, Finset.inter_eq_left.mpr hAU,
    Finset.sum_const, nsmul_eq_mul, hcard]
  ring

theorem sum_norm_balanced_cover_bounds {N : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (hAU : A ⊆ U) :
    (∑ x ∈ U, ‖balanced A x‖) ≤ 2 * density A * (1 - density A) * N ∧
    (∑ x ∈ U, ‖balanced A x‖) ≤ 2 * (U.card : Real) * (1 - density A) := by
  have hd := density_nonneg A
  have hd1 := density_le_one A
  have hU : (U.card : Real) ≤ N := by
    exact_mod_cast (show U.card ≤ N by simpa only [ZMod.card] using U.card_le_univ)
  have hA : density A * (N : Real) ≤ U.card := by
    have hc : density A * (N : Real) = A.card :=
      div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)
    rw [hc]
    exact_mod_cast Finset.card_le_card hAU
  rw [sum_norm_balanced_on_cover A U hAU]
  have hfirst : density A * ((N : Real) + U.card - 2 * density A * N) ≤
      2 * density A * (1 - density A) * N := by
    nlinarith [mul_le_mul_of_nonneg_left hU hd]
  refine ⟨hfirst, hfirst.trans ?_⟩
  have h := mul_le_mul_of_nonneg_right hA (sub_nonneg.mpr hd1)
  nlinarith [h]

theorem cover_phase_correlation_le_mass {N m : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin m → Finset (ZMod N))
    (z : Fin m → ZMod N → Complex) (hP : IsPartition P U)
    (hz : ∀ i x, ‖z i x‖ ≤ 1) :
    (∑ i, ‖∑ x ∈ P i, balanced A x * z i x‖) ≤ ∑ x ∈ U, ‖balanced A x‖ := by
  calc
    _ ≤ ∑ i, ∑ x ∈ P i, ‖balanced A x‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hz i x)
    _ = _ := hP.sum_values _

theorem cover_correlation_density_bounds {N m : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin m → Finset (ZMod N))
    (z : Fin m → ZMod N → Complex) (hP : IsPartition P U) (hAU : A ⊆ U)
    (hz : ∀ i x, ‖z i x‖ ≤ 1) {alpha : Real}
    (ha : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * z i x‖) :
    alpha ≤ 2 * density A * (1 - density A) ∧
      alpha * N ≤ 2 * (U.card : Real) * (1 - density A) := by
  have hmass := ha.trans (cover_phase_correlation_le_mass A U P z hP hz)
  obtain ⟨hfirst, hsecond⟩ := sum_norm_balanced_cover_bounds A U hAU
  refine ⟨?_, hmass.trans hsecond⟩
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast NeZero.pos N : (0 : Real) < N)).mp
    (hmass.trans hfirst)

theorem cover_correlation_density_strict {N m : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin m → Finset (ZMod N))
    (z : Fin m → ZMod N → Complex) (hP : IsPartition P U) (hAU : A ⊆ U)
    (hz : ∀ i x, ‖z i x‖ ≤ 1) {alpha : Real} (ha0 : 0 < alpha)
    (ha : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * z i x‖) :
    0 < density A ∧ density A < 1 := by
  have hb := (cover_correlation_density_bounds A U P z hP hAU hz ha).1
  have hd := density_nonneg A
  have hd1 := density_le_one A
  constructor <;> nlinarith

theorem comparable_partition_card_bound {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (U : Finset X) (hP : IsPartition P U)
    (hcomp : ∀ i j, (P i).card ≤ 2 * (P j).card) (j : Fin m) :
    U.card ≤ 2 * m * (P j).card := by
  rw [← hP.sum_card]
  calc
    _ ≤ ∑ _i : Fin m, 2 * (P j).card := Finset.sum_le_sum fun i _ => hcomp i j
    _ = _ := by simp; ring

end LeanProofs.GowersSzemeredi
