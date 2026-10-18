import GowersSzemeredi.Proofs08QuadraticFrequencies
import GowersSzemeredi.Proofs18IntervalCubeEnergy
import GowersSzemeredi.Proofs17PartitionEnergy

/-! Retaining the total Fourier bias of a nonuniform progression partition.
The support size, rather than the ambient modulus, controls the energy. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ZMod
namespace LeanProofs.GowersSzemeredi

/-- Fourier expansion of a function restricted to a finite cell. -/
theorem fourier_restrictToCell {N : Nat} [NeZero N] (S : Finset (ZMod N))
    (f : ZMod N → Complex) (r : ZMod N) :
    fourier (restrictToCell S f) r =
      ∑ x ∈ S, f x * exponential (-(r * x)) := by
  rw [fourier, ZMod.dft_apply]
  simp only [restrictToCell, smul_eq_mul, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro x _
  simp only [exponential, mul_comm]

/-- The Fourier transform of a disc-valued function supported on S has
norm bounded by the actual cardinality of S. -/
theorem norm_fourier_restrictToCell_le {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (f : ZMod N → Complex) (hf : DiscValued f) (r : ZMod N) :
    ‖fourier (restrictToCell S f) r‖ ≤ S.card := by
  rw [fourier_restrictToCell]
  calc
    _ ≤ ∑ x ∈ S, ‖f x * exponential (-(r * x))‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ S, (1 : Real) := by
      apply Finset.sum_le_sum
      intro x _
      have he : ‖exponential (-(r * x))‖ = 1 := (ZMod.stdAddChar (N := N)).norm_apply _
      simpa only [norm_mul, he, mul_one] using hf x
    _ = _ := by simp

/-- Support-sensitive energy bound by a maximizing Fourier coefficient.
This retains a single power of that coefficient, useful when summing cells. -/
theorem exists_fourier_restrict_energy_bound {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (f : ZMod N → Complex) (hf : DiscValued f) :
    ∃ r : ZMod N,
      (∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference (restrictToCell S f) a s‖ ^ 2) ≤
        (S.card : Real) ^ 2 * ‖fourier (restrictToCell S f) r‖ := by
  let g := restrictToCell S f
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun r ↦ ‖fourier g r‖)
    Finset.univ_nonempty
  have hpoint (t : ZMod N) : ‖fourier g t‖ ^ 2 ≤ ‖fourier g r‖ * S.card := by
    simpa only [pow_two] using mul_le_mul (hr t (Finset.mem_univ _))
      (norm_fourier_restrictToCell_le S f hf t) (norm_nonneg _) (norm_nonneg _)
  have hparseval : ∑ t : ZMod N, ‖fourier g t‖ ^ 2 ≤ (N : Real) * S.card := by
    rw [identity_2_3_holds]
    gcongr
    simp only [g, restrictToCell, apply_ite, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_ite_mem_eq]
    exact (Finset.sum_le_sum fun s _ => pow_le_one₀ (norm_nonneg _) (hf s)).trans_eq (by simp)
  have hfour : ∑ t : ZMod N, ‖fourier g t‖ ^ 4 ≤
      (N : Real) * ((S.card : Real) ^ 2 * ‖fourier g r‖) :=
    calc _ ≤ ∑ t : ZMod N, ‖fourier g r‖ * S.card * ‖fourier g t‖ ^ 2 :=
          Finset.sum_le_sum fun t _ => by
            linarith only [mul_le_mul_of_nonneg_right (hpoint t) (sq_nonneg ‖fourier g t‖)]
      _ = ‖fourier g r‖ * S.card * ∑ t : ZMod N, ‖fourier g t‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ‖fourier g r‖ * S.card * (N * S.card) := by gcongr
      _ = _ := by ring
  rw [fourthMoment_eq_degreeOneEnergy] at hfour
  exact ⟨r, (mul_le_mul_iff_right₀ (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).mp hfour⟩

/-- Partition nonuniformity of degree one gives total Fourier correlation
at least beta times the ambient size. No prime-model or selected-cell loss
is needed: every cell supplies its own frequency. -/
theorem partition_linear_nonuniformity_fourier_bias {N K m : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin K → ModAP N) (beta : Real)
    (hf : DiscValued f) (hβ : 0 ≤ beta)
    (hpart : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hsize : ∀ i, (Q i).carrier.card ≤ m)
    (hfail : ¬ UniformOnPartition f 1 beta Q m) :
    ∃ r : Fin K → ZMod N,
      beta * N < ∑ i, ‖∑ x ∈ (Q i).carrier, f x * exponential (-(r i * x))‖ := by
  have henergy : beta * (m : Real) ^ 3 * K < ∑ i, ∑ a : Point N 1,
      ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2 := by
    unfold UniformOnPartition at hfail
    simp only [sum_cube_succ_eq_sum_norm_sq, Complex.ofReal_re, Nat.reduceAdd] at hfail
    exact lt_of_not_ge hfail
  choose r hr using fun i ↦ exists_fourier_restrict_energy_bound (Q i).carrier f hf
  have hbound : (∑ i, ∑ a : Point N 1,
      ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2) ≤
      (m : Real) ^ 2 * ∑ i, ‖fourier (restrictToCell (Q i).carrier f) (r i)‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hr i).trans (by gcongr; exact_mod_cast hsize i)
  have htotal : (N : Real) ≤ m * K := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) ↦ hsize i)
    rw [hpart.sum_card] at h
    exact_mod_cast (by simpa [mul_comm] using h : N ≤ m * K)
  refine ⟨r, lt_of_mul_lt_mul_left ?_ (sq_nonneg (m : Real))⟩
  simp_rw [← fourier_restrictToCell]
  have h0 : (0 : Real) ≤ beta * m ^ 2 := by positivity
  linarith only [henergy.trans_le hbound, mul_le_mul_of_nonneg_left htotal h0]

end LeanProofs.GowersSzemeredi
