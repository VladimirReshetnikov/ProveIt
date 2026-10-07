import GowersSzemeredi.Proofs03SupportEnergy
import GowersSzemeredi.Proofs17PartitionEnergy

/-! Failure of partition uniformity survives on cells containing a positive
fraction of the ambient mass. The estimate does not require equal lengths. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- The support estimate for the extension by zero of a disc-valued function. -/
theorem restrictToCell_uniformEnergy_le {N k : Nat} [NeZero N]
    {f : ZMod N → Complex} (hf : DiscValued f) (S : Finset (ZMod N)) :
    (∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (restrictToCell S f) a s‖ ^ 2) ≤
      (S.card : Real) ^ (k + 2) :=
  uniformEnergy_le_support_pow (restrictToCell_discValued hf S) S
    (fun x hx => by simp [restrictToCell, hx])

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
  classical
  let E : Fin M → Real := fun i =>
    ∑ a : Point N k, ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2
  let t : Real := beta / 2 * (m : Real) ^ (k + 2)
  let B : Finset (Fin M) := Finset.univ.filter (fun i => t < E i)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have henergy : beta * (m : Real) ^ (k + 2) * M < ∑ i, E i := by
    unfold UniformOnPartition at hfail
    simp only [sum_cube_succ_eq_sum_norm_sq, Complex.ofReal_re] at hfail
    exact lt_of_not_ge hfail
  have hE (i : Fin M) : E i ≤ (m : Real) ^ (k + 1) * (Q i).carrier.card := by
    calc
      E i ≤ ((Q i).carrier.card : Real) ^ (k + 2) := restrictToCell_uniformEnergy_le hf _
      _ = ((Q i).carrier.card : Real) ^ (k + 1) * (Q i).carrier.card := pow_succ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsize i) _) (by positivity)
  have hbound : (∑ i, E i) ≤ t * M + (m : Real) ^ (k + 1) *
      ∑ i ∈ B, ((Q i).carrier.card : Real) := by
    calc
      _ ≤ ∑ i : Fin M, (t + if i ∈ B then (m : Real) ^ (k + 1) *
          (Q i).carrier.card else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ B
        · rw [if_pos hi]
          exact (hE i).trans (le_add_of_nonneg_left ht)
        · rw [if_neg hi, add_zero]
          exact le_of_not_gt (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.sum_filter]
        have hfilter : Finset.univ.filter (fun i => i ∈ B) = B := by ext i; simp
        rw [hfilter, ← Finset.mul_sum]
        ring
  have hmass : beta / 2 * ((m : Real) * M) <
      ∑ i ∈ B, ((Q i).carrier.card : Real) := by
    have hp : 0 < (m : Real) ^ (k + 1) := by positivity
    apply (mul_lt_mul_iff_right₀ hp).mp
    have heq : beta * (m : Real) ^ (k + 2) * M =
        2 * t * M := by dsimp [t]; ring
    have heq' : (m : Real) ^ (k + 1) * (beta / 2 * ((m : Real) * M)) = t * M := by
      dsimp [t]
      rw [pow_succ]
      ring
    rw [heq']
    rw [heq] at henergy
    linarith
  have htotal : (N : Real) ≤ (m : Real) * M := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) => hsize i)
    rw [hpart.sum_card] at h
    have hn : N ≤ m * M := by simpa [mul_comm] using h
    exact_mod_cast hn
  refine ⟨B, (mul_le_mul_of_nonneg_left htotal (by positivity)).trans_lt hmass, ?_⟩
  intro i hi hu
  have hi' : t < E i := (Finset.mem_filter.mp hi).2
  have hNne : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hscale : (beta / 2 * ((m : Real) / N) ^ (k + 2)) * (N : Real) ^ (k + 2) = t := by
    dsimp [t]
    rw [div_pow]
    field_simp
  unfold UniformOfDegree at hu
  rw [hscale] at hu
  exact not_lt_of_ge hu hi'

end LeanProofs.GowersSzemeredi
