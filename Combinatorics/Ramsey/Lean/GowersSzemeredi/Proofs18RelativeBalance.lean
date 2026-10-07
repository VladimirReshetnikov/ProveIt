import GowersSzemeredi.Proofs18QuadraticDensityIncrement

/-! Balance relative to a specified support, rather than the entire cyclic
group. This keeps the original interval density under a cyclic embedding. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The real function 1_A-delta*1_S, extended by zero outside the support. -/
def relativeBalancedReal {N : Nat} (A S : Finset (ZMod N)) (delta : Real)
    (x : ZMod N) : Real :=
  (if x ∈ A then 1 else 0) - delta * (if x ∈ S then 1 else 0)

/-- The same relative balance in the complex convention used by uniformity. -/
def relativeBalanced {N : Nat} (A S : Finset (ZMod N)) (delta : Real) : ZMod N → Complex :=
  fun x ↦ (relativeBalancedReal A S delta x : Complex)

theorem relativeBalanced_eq_indicators {N : Nat} (A S : Finset (ZMod N)) (delta : Real)
    (x : ZMod N) : relativeBalanced A S delta x = indicator A x - (delta : Complex) * indicator S x := by
  classical
  by_cases hxA : x ∈ A <;> by_cases hxS : x ∈ S <;>
    simp [relativeBalanced, relativeBalancedReal, indicator, hxA, hxS]

/-- No spurious constant background remains outside the original support. -/
theorem relativeBalancedReal_eq_zero_outside {N : Nat} (A S : Finset (ZMod N))
    (delta : Real) (hAS : A ⊆ S) {x : ZMod N} (hx : x ∉ S) :
    relativeBalancedReal A S delta x = 0 := by
  have hxA : x ∉ A := fun h ↦ hx (hAS h)
  simp [relativeBalancedReal, hxA, hx]

theorem relativeBalancedReal_abs_le_one {N : Nat} (A S : Finset (ZMod N))
    (delta : Real) (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) :
    ∀ x, |relativeBalancedReal A S delta x| ≤ 1 := by
  intro x
  by_cases hxA : x ∈ A
  · simp only [relativeBalancedReal, if_pos hxA, if_pos (hAS hxA), mul_one]
    rw [abs_of_nonneg (sub_nonneg.mpr hδone)]
    linarith only [hδ]
  · by_cases hxS : x ∈ S
    · simpa [relativeBalancedReal, hxA, hxS, abs_of_nonneg hδ] using hδone
    · simp [relativeBalancedReal, hxA, hxS]

theorem relativeBalanced_discValued {N : Nat} (A S : Finset (ZMod N))
    (delta : Real) (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) :
    DiscValued (relativeBalanced A S delta) := by
  intro x
  simpa only [relativeBalanced, Complex.norm_real, Real.norm_eq_abs] using
    relativeBalancedReal_abs_le_one A S delta hAS hδ hδone x

/-- Cell discrepancy is measured against support mass in the cell. -/
theorem relativeBalancedReal_sum {N : Nat} (A S T : Finset (ZMod N)) (delta : Real) :
    ∑ x ∈ T, relativeBalancedReal A S delta x =
      ((A ∩ T).card : Real) - delta * (S ∩ T).card := by
  classical
  have hindicator (B : Finset (ZMod N)) :
      (∑ x ∈ T, if x ∈ B then (1 : Real) else 0) = (B ∩ T).card := by
    rw [← Finset.sum_filter]
    have heq : T.filter (fun x ↦ x ∈ B) = B ∩ T := by ext x; simp [and_comm]
    rw [heq]
    simp
  simp only [relativeBalancedReal, Finset.sum_sub_distrib, ← Finset.mul_sum, hindicator]

/-- The relative cardinality identity gives exact mean zero in any modulus. -/
theorem relativeBalancedReal_sum_zero {N : Nat} [NeZero N] (A S : Finset (ZMod N))
    (delta : Real) (hcard : (A.card : Real) = delta * S.card) :
    ∑ x : ZMod N, relativeBalancedReal A S delta x = 0 := by
  simpa only [Finset.inter_univ, hcard, sub_self] using relativeBalancedReal_sum A S Finset.univ delta

/-- The usual cyclic balance is the special case of full support. -/
theorem relativeBalanced_univ {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    relativeBalanced A Finset.univ (density A) = balanced A := by
  funext x
  rw [relativeBalanced_eq_indicators]
  simp [indicator, balanced]

/-- A discrepancy partition yields an increment relative to the original
support, on its intersection with one cell. The intersection need not be an
arithmetic progression. Its mass retains a second factor of the increment. -/
theorem relative_density_increment_of_discrepancy_partition {N M : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (delta beta s : Real) (P : Fin M → ModAP N)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hβ : 0 ≤ beta)
    (hcard : (A.card : Real) = delta * S.card)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (havg : s ≤ averageCellSize (fun i ↦ (P i).carrier))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (P i).carrier, relativeBalanced A S delta x‖) :
    ∃ j : Fin M,
      beta / 4 * s ≤ ((P j).carrier.card : Real) ∧
      (beta / 4) ^ 2 * s ≤ ((S ∩ (P j).carrier).card : Real) ∧
      (delta + beta / 4) * (S ∩ (P j).carrier).card ≤ (A ∩ (P j).carrier).card := by
  have hM := section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpart
  have hdisReal : beta * N ≤ ∑ i, |∑ x ∈ (P i).carrier, relativeBalancedReal A S delta x| := by
    simpa only [relativeBalanced, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hdis
  obtain ⟨j, hinc, hsize⟩ := lemma_5_15_holds N M (relativeBalancedReal A S delta)
    (fun i ↦ (P i).carrier) beta hM hβ
    (relativeBalancedReal_abs_le_one A S delta hAS hδ hδone)
    (relativeBalancedReal_sum_zero A S delta hcard) hpart hdisReal
  have hPsize : beta / 4 * s ≤ ((P j).carrier.card : Real) := by
    calc
      _ ≤ beta / 4 * averageCellSize (fun i ↦ (P i).carrier) :=
        mul_le_mul_of_nonneg_left havg (by positivity)
      _ = beta * N / (4 * M) := by rw [hpart.averageCellSize_univ]; ring
      _ ≤ _ := hsize
  rw [relativeBalancedReal_sum] at hinc
  have hsub : ((A ∩ (P j).carrier).card : Real) ≤ (S ∩ (P j).carrier).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right hAS)
  have hcap : ((S ∩ (P j).carrier).card : Real) ≤ (P j).carrier.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hmass : beta / 4 * ((P j).carrier.card : Real) ≤ (S ∩ (P j).carrier).card := by
    have hnonneg : 0 ≤ delta * ((S ∩ (P j).carrier).card : Real) := by positivity
    nlinarith only [hinc, hsub, hnonneg]
  refine ⟨j, hPsize, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hPsize (by positivity : 0 ≤ beta / 4)
    nlinarith only [hm, hmass]
  · have hm := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ beta / 4)
    nlinarith only [hinc, hm]

end LeanProofs.GowersSzemeredi
