import GowersSzemeredi.Proofs05PhaseRemoval

/-! Declarations of `Proofs05PhaseRemoval` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor57_sum_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (S : Finset X) (hpartition : IsPartition P S)
    (g : X → Complex) :
    ∑ j, ∑ x ∈ P j, g x = ∑ x ∈ S, g x := by
  have hpair : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    exact hpartition.2 i j (bne_iff_ne.mpr hij)
  have hunion : (Finset.univ : Finset (Fin m)).biUnion P = S := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact (hpartition.1 x).symm
  rw [show (∑ j, ∑ x ∈ P j, g x) =
      ∑ j ∈ (Finset.univ : Finset (Fin m)), ∑ x ∈ P j, g x by simp]
  rw [← Finset.sum_biUnion hpair, hunion]

private lemma cor57_card_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (S : Finset X) (hpartition : IsPartition P S) :
    ∑ j, (P j).card = S.card := by
  apply Nat.cast_injective (R := Complex)
  calc
    ((∑ j, (P j).card : Nat) : Complex) =
        ∑ j, ∑ _x ∈ P j, (1 : Complex) := by simp
    _ = ∑ _x ∈ S, (1 : Complex) :=
      cor57_sum_partition P S hpartition _
    _ = (S.card : Complex) := by simp

private lemma cor57_alpha_le_one {N r : Nat} [NeZero N]
    (f : ZMod N → Complex) (phi : ZMod N → ZMod N) (alpha : Real)
    (hr : 0 < r) (hf : DiscValued f)
    (hpremise : alpha * r ≤
      ‖∑ x ∈ Finset.range r,
        f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖) :
    alpha ≤ 1 := by
  have hnorm :
      ‖∑ x ∈ Finset.range r,
        f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖ ≤ r := by
    calc
      _ ≤ ∑ x ∈ Finset.range r,
          ‖f (x : ZMod N) * exponential (-(phi (x : ZMod N)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _x ∈ Finset.range r, (1 : Real) := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul, cor57_norm_exponential, mul_one]
        exact hf _
      _ = r := by simp
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  nlinarith

private lemma cor57_scale_lt {k r : Nat} (alpha : Real)
    (halpha : 0 < alpha)
    (hlarge :
      (4 * Real.pi / alpha) ^ polynomialPartitionConstant k < (r : Real)) :
    (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) <
      alpha / (4 * Real.pi) := by
  let K := polynomialPartitionConstant k
  have hK : 0 < K := cor57_partition_constant_pos k
  have hKReal : (0 : Real) < K := by exact_mod_cast hK
  have hr : (0 : Real) < r := by
    have hbase : 0 < 4 * Real.pi / alpha := by positivity
    exact (pow_nonneg hbase.le K).trans_lt hlarge
  have hbase : 0 < 4 * Real.pi / alpha := by positivity
  have hroot : 4 * Real.pi / alpha < (r : Real) ^ (K : Real)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos hbase.le hr.le hKReal]
    simpa only [Real.rpow_natCast] using hlarge
  have hrootPos : 0 < (r : Real) ^ (K : Real)⁻¹ :=
    Real.rpow_pos_of_pos hr _
  have hinv : ((r : Real) ^ (K : Real)⁻¹)⁻¹ <
      (4 * Real.pi / alpha)⁻¹ :=
    (inv_lt_inv₀ hrootPos hbase).2 hroot
  rw [Real.rpow_neg hr.le]
  have hright : (4 * Real.pi / alpha)⁻¹ = alpha / (4 * Real.pi) := by
    field_simp
  simpa only [K, hright] using hinv

/-- The analytic part of Corollary 5.7, conditional only on the corrected
target-length form of Corollary 5.6. -/
theorem corollary_5_7_holds_of_corollary_5_6
    (h56 : corollary_5_6) : corollary_5_7 := by
  intro N k r v _ phi alpha hk hphi halpha hlarge hrN hv hvupper
  have hthreshold : polynomialPartitionThreshold k < r := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hlarge)
  obtain ⟨M, P, hM, hpartition, hproper, hdiameter⟩ :=
    h56 N k r v phi hk hphi hthreshold hrN hv hvupper
  refine ⟨M, P, hM, hpartition, hproper, ?_⟩
  intro f hf hpremise
  have hpolyLarge :
      (4 * Real.pi / alpha) ^ polynomialPartitionConstant k < (r : Real) :=
    lt_of_le_of_lt (le_max_right _ _) hlarge
  have hscale :
      (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N ≤
        alpha * N / (4 * Real.pi) := by
    have := (cor57_scale_lt alpha halpha hpolyLarge).le
    have hN : (0 : Real) ≤ N := by positivity
    calc
      (r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N ≤
          (alpha / (4 * Real.pi)) * N := mul_le_mul_of_nonneg_right this hN
      _ = alpha * N / (4 * Real.pi) := by ring
  have hcell (j : Fin M) :
      ‖∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ ≤
        ‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ +
          alpha / 2 * (P j).carrier.card :=
    cor57_cell_norm_le (P j).carrier f phi alpha
      ((r : Real) ^ (-(polynomialPartitionConstant k : Real)⁻¹) * N)
      hf (hdiameter j) hscale
  have htwisted :
      (∑ j, ∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))) =
        ∑ s ∈ Finset.range r,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N))) :=
    cor57_sum_partition (fun j => (P j).carrier) (Finset.range r)
      hpartition _
  have hcards :
      ∑ j, ((P j).carrier.card : Real) = r := by
    have hc := cor57_card_partition (fun j => (P j).carrier)
      (Finset.range r) hpartition
    rw [Finset.card_range] at hc
    exact_mod_cast hc
  calc
    alpha / 2 * r ≤ alpha * r - alpha / 2 * r := by
      ring_nf
      exact le_rfl
    _ ≤ ‖∑ s ∈ Finset.range r,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ -
        alpha / 2 * r := sub_le_sub_right hpremise _
    _ = ‖∑ j, ∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖ -
        alpha / 2 * r := by rw [htwisted]
    _ ≤ (∑ j, ‖∑ s ∈ (P j).carrier,
          f (s : ZMod N) * exponential (-(phi (s : ZMod N)))‖) -
        alpha / 2 * r := by gcongr; exact norm_sum_le _ _
    _ ≤ (∑ j, (‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ +
          alpha / 2 * (P j).carrier.card)) - alpha / 2 * r := by
      gcongr
      exact hcell _
    _ = ∑ j, ‖∑ s ∈ (P j).carrier, f (s : ZMod N)‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcards]
      ring

end LeanProofs.GowersSzemeredi
