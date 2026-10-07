import GowersSzemeredi.Proofs18SelectedRefinement
import GowersSzemeredi.Proofs18PartitionPrimeModels

/-! Assemble an inverse theorem of any degree in the prime models of
selected cells. Both the total discrepancy and the count include the
unselected cells; no inverse theorem in the ambient degree is assumed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- The full count constant for transport from comparable prime models. -/
def localInverseAssemblyConstant (ratio sigma : Real) : Real :=
  max 1 (2 * boundaryRefinementConstant (1 / 16) * ratio ^ (1 - sigma / 16))

/-- Apply an arbitrary-degree inverse theorem on all selected prime models
and assemble a proper partition of the entire original cyclic group. -/
theorem FunctionDiscrepancyBound.selected_prime_model_partition
    {degree N K l : Nat} [NeZero N]
    {alpha beta sigma T ratio : Real}
    (hbound : FunctionDiscrepancyBound degree alpha beta sigma T)
    (hβ : 0 ≤ beta) (hσ : 0 ≤ sigma) (hσ16 : sigma ≤ 16) (hratio : 0 ≤ ratio)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (Q : Fin K → ModAP N) (B : Finset (Fin K))
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper) (hl : 1 ≤ l)
    (hli : ∀ i, l ≤ (Q i).length)
    (hmodels : ∀ i ∈ B, ∃ M : Nat, ∃ hM : M.Prime,
      letI : NeZero M := ⟨hM.ne_zero⟩
      4 ≤ M ∧ (Q i).length ≤ M ∧ T ≤ (M : Real) ∧
      (M : Real) ≤ ratio * (Q i).length ∧
      ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction f)) alpha degree) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (J : Real) ≤ localInverseAssemblyConstant ratio sigma * N / (l : Real) ^ (sigma / 16) ∧
      beta * (∑ i ∈ B, ((Q i).carrier.card : Real)) ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  let t := sigma / 16
  let D := localInverseAssemblyConstant ratio sigma
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htone : t ≤ 1 := by dsimp [t]; linarith only [hσ16]
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hC : 0 < boundaryRefinementConstant (1 / 16) := section5LocalRefinementConstant_pos _ _
  have hlone : (1 : Real) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : Real) < l := zero_lt_one.trans_le hlone
  have hli' (i : Fin K) : (l : Real) ≤ (Q i).carrier.card := by
    rw [hproper i]
    exact_mod_cast hli i
  let budget : Fin K → Real := fun i => D * (Q i).carrier.card / (l : Real) ^ t
  have hbudget (i : Fin K) : 1 ≤ budget i := by
    calc
      _ ≤ ((Q i).carrier.card : Real) / (l : Real) ^ t := one_le_linear_scale hlone (hli' i) htone
      _ ≤ _ := by
        dsimp [budget]
        exact div_le_div_of_nonneg_right
          (by nlinarith only [mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (Q i).carrier.card)])
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hlocal (i : Fin K) (hi : i ∈ B) : ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) (Q i).carrier ∧
      (∀ j, (R j).IsProper) ∧ (J : Real) ≤ budget i ∧
      beta * (Q i).carrier.card ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
    obtain ⟨M, hM, hMfour, hMlow, hT, hMup, hnon⟩ := hmodels i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    letI : Fact M.Prime := ⟨hM⟩
    obtain ⟨J, R, hR, hRproper, hcount, hdis⟩ :=
      hbound.progression_partition (Q i) (hproper i) hMfour hMlow hT f hf hnon
    have hMreal : (M : Real) ≤ ratio * (Q i).carrier.card := by rwa [hproper i]
    have hpower : (M : Real) ^ (1 - t) ≤ ratio ^ (1 - t) * ((Q i).carrier.card : Real) ^ (1 - t) := by
      rw [← Real.mul_rpow hratio (Nat.cast_nonneg _)]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMreal (by linarith only [htone])
    refine ⟨J, R, hR, hRproper, ?_, ?_⟩
    · calc
        (J : Real) ≤ 2 * boundaryRefinementConstant (1 / 16) * (M : Real) ^ (1 - t) := hcount
        _ ≤ 2 * boundaryRefinementConstant (1 / 16) *
            (ratio ^ (1 - t) * ((Q i).carrier.card : Real) ^ (1 - t)) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ ≤ D * ((Q i).carrier.card : Real) ^ (1 - t) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ D * (((Q i).carrier.card : Real) / (l : Real) ^ t) :=
          mul_le_mul_of_nonneg_left (rpow_count_le_linear_scale hlpos (hli' i) ht) hD0
        _ = budget i := by dsimp [budget]; ring
    · apply le_trans _ hdis
      apply mul_le_mul_of_nonneg_left _ hβ
      rw [hproper i]
      exact_mod_cast hMlow
  obtain ⟨J, R, hR, _, hRproper, hcount, hdis⟩ := selected_discrepancy_refinement
    Q f B budget beta hQ hproper hbudget hlocal
  refine ⟨J, R, hR, hRproper, ?_, hdis⟩
  apply hcount.trans_eq
  dsimp [budget]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, hQ.sum_card]
  simp [D, t]

/-- A localized uniformity obstruction supplies the selected prime models
and their mass automatically, in any degree. The only inverse hypothesis
is in the degree of that localized obstruction. -/
theorem FunctionDiscrepancyBound.localized_partition
    {degree N K l m : Nat} [NeZero N] [Fact N.Prime]
    {eta beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound degree
      ((eta / 2) / (2 * (degree + 2 : Nat) : Real) ^ (degree + 2)) beta sigma T)
    (hη : 0 ≤ eta) (hβ : 0 ≤ beta) (hσ : 0 ≤ sigma) (hσ16 : sigma ≤ 16)
    (f : ZMod N → Complex) (hf : DiscValued f) (Q : Fin K → ModAP N)
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper) (hl : 2 ≤ l) (hT : T ≤ (l : Real)) (hm : 0 < m)
    (hlength : ∀ i, l ≤ (Q i).length ∧ (Q i).length ≤ m ∧ (degree + 2) * (Q i).length ≤ N)
    (hfail : ¬ UniformOnPartition f degree eta Q m) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (J : Real) ≤ localInverseAssemblyConstant (2 * (degree + 2 : Nat)) sigma * N /
        (l : Real) ^ (sigma / 16) ∧
      (eta * beta / 2) * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  obtain ⟨B, hmass, hB⟩ := partition_nonuniformity_prime_models f Q eta hf hη hm hQ hproper
    (fun i => ⟨hl.trans (hlength i).1, (hlength i).2⟩) hfail
  have hmodels (i : Fin K) (hi : i ∈ B) : ∃ M : Nat, ∃ hM : M.Prime,
      letI : NeZero M := ⟨hM.ne_zero⟩
      4 ≤ M ∧ (Q i).length ≤ M ∧ T ≤ (M : Real) ∧
      (M : Real) ≤ (2 * (degree + 2 : Nat) : Real) * (Q i).length ∧
      ¬ UniformOfDegree (intervalExtension M ((Q i).pullbackFunction f))
        ((eta / 2) / (2 * (degree + 2 : Nat) : Real) ^ (degree + 2)) degree := by
    obtain ⟨M, hM, hMlow, hMup, _, hnon⟩ := hB i hi
    letI : NeZero M := ⟨hM.ne_zero⟩
    have hLM : (Q i).length ≤ M := by
      have h := Nat.le_mul_of_pos_left (Q i).length (by omega : 0 < degree + 2)
      omega
    have hfour : 4 ≤ M := by
      have hh : 2 * (Q i).length ≤ (degree + 2) * (Q i).length := Nat.mul_le_mul_right _ (by omega)
      have hlen := (hlength i).1
      omega
    refine ⟨M, hM, hfour, hLM, hT.trans ?_, ?_, hnon⟩
    · exact_mod_cast (hlength i).1.trans hLM
    · exact_mod_cast (show M ≤ (2 * (degree + 2)) * (Q i).length by simpa only [Nat.mul_assoc] using hMup)
  obtain ⟨J, R, hR, hp, hc, hd⟩ := hbound.selected_prime_model_partition hβ hσ hσ16
    (by positivity : (0 : Real) ≤ (2 * (degree + 2 : Nat) : Real)) f hf Q B hQ hproper (by omega) (fun i => (hlength i).1) hmodels
  refine ⟨J, R, hR, hp, hc, ?_⟩
  have h := mul_le_mul_of_nonneg_left hmass.le hβ
  exact (by nlinarith only [h] : (eta * beta / 2) * N ≤ beta * ∑ i ∈ B, ((Q i).carrier.card : Real)).trans hd

end LeanProofs.GowersSzemeredi
