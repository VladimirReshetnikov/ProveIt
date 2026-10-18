import GowersSzemeredi.Proofs03SupportEnergy
import GowersSzemeredi.Proofs17PartitionEnergy

/-! Failure of partition uniformity survives on cells containing a positive
fraction of the ambient mass. The estimate does not require equal lengths. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- If a partition fails degree-k uniformity at beta, cells failing at half
that local parameter contain more than beta/2 of the total ambient mass.
There is no dependence on the number of cells in this mass fraction. -/
theorem not_uniformOnPartition_nonuniform_cell_mass {N M k m : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin M → ModAP N) (beta : Real)
    (hf : DiscValued f) (hβ : 0 ≤ beta) (hm : 0 < m)
    (hpart : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hsize : ∀ i, (Q i).carrier.card ≤ m)
    (hfail : ¬ UniformOnPartition f k beta Q m) :
    ∃ B : Finset (Fin M),
      beta / 2 * N < ∑ i ∈ B, ((Q i).carrier.card : Real) ∧
      ∀ i ∈ B, ¬ UniformOfDegree (restrictToCell (Q i).carrier f)
        (beta / 2 * ((m : Real) / N) ^ (k + 2)) k := by
  let E : Fin M → Real := fun i =>
    ∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2
  let t : Real := beta / 2 * (m : Real) ^ (k + 2)
  let B : Finset (Fin M) := Finset.univ.filter (fun i => t < E i)
  have henergy : beta * (m : Real) ^ (k + 2) * M < ∑ i, E i := by
    unfold UniformOnPartition at hfail
    simp only [sum_cube_succ_eq_sum_norm_sq, Complex.ofReal_re] at hfail
    exact lt_of_not_ge hfail
  -- a cell carries energy at most `t` outside `B` and at most `m^(k+1)·|Q i|` inside
  have hbound : ∑ i, E i ≤
      ∑ i, (t + if i ∈ B then (m : Real) ^ (k + 1) * (Q i).carrier.card else 0) := by
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with hi
    · refine le_add_of_nonneg_of_le (by positivity) ((uniformEnergy_le_support_pow
        (restrictToCell_discValued hf _) (Q i).carrier fun x hx => by
          simp [restrictToCell, hx]).trans ?_)
      rw [pow_succ _ (k + 1)]
      gcongr
      exact_mod_cast hsize i
    · simpa using not_lt.mp fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hbound
  have hmass : beta / 2 * ((m : Real) * M) < ∑ i ∈ B, ((Q i).carrier.card : Real) := by
    refine lt_of_mul_lt_mul_left ?_ (by positivity : (0 : Real) ≤ (m : Real) ^ (k + 1))
    have h : (m : Real) ^ (k + 2) = (m : Real) ^ (k + 1) * m := pow_succ _ _
    simp only [t, h] at hbound henergy
    linarith
  have htotal : (N : Real) ≤ m * M := by
    have h := Finset.sum_le_card_nsmul Finset.univ _ m fun i _ => hsize i
    rw [hpart.sum_card] at h
    exact_mod_cast (by simpa [mul_comm] using h : N ≤ m * M)
  refine ⟨B, (mul_le_mul_of_nonneg_left htotal (by positivity)).trans_lt hmass, fun i hi hu => ?_⟩
  have hNne : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold UniformOfDegree at hu
  rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hNne)] at hu
  exact not_lt_of_ge hu (Finset.mem_filter.mp hi).2

end LeanProofs.GowersSzemeredi
