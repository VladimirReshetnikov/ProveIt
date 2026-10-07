import GowersSzemeredi.Proofs18LinearFourierObstruction
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
  classical
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

/-- Exact fourth-moment identity in the cube-coordinate convention. -/
theorem fourthMoment_eq_degreeOneEnergy {N : Nat} [NeZero N]
    (f : ZMod N → Complex) :
    ∑ r : ZMod N, ‖fourier f r‖ ^ 4 =
      (N : Real) * ∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2 := by
  have hs := (pointOneEquiv N).sum_comp
    (fun a : Point N 1 ↦ ‖∑ s : ZMod N, cubeDifference f a s‖ ^ 2)
  simp only [cubeDifference_pointOne] at hs
  rw [← hs]
  have h := lemma_2_1_holds N f f
  simpa only [difference, ← pow_add] using h

/-- Support-sensitive energy bound by a maximizing Fourier coefficient.
This retains a single power of that coefficient, useful when summing cells. -/
theorem exists_fourier_restrict_energy_bound {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (f : ZMod N → Complex) (hf : DiscValued f) :
    ∃ r : ZMod N,
      (∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference (restrictToCell S f) a s‖ ^ 2) ≤
        (S.card : Real) ^ 2 * ‖fourier (restrictToCell S f) r‖ := by
  classical
  let g := restrictToCell S f
  obtain ⟨r, _, hr⟩ := Finset.exists_max_image Finset.univ (fun r ↦ ‖fourier g r‖)
    Finset.univ_nonempty
  have hpoint (t : ZMod N) : ‖fourier g t‖ ^ 2 ≤ ‖fourier g r‖ * S.card := by
    simpa only [pow_two] using mul_le_mul (hr t (Finset.mem_univ _))
      (norm_fourier_restrictToCell_le S f hf t) (norm_nonneg _) (norm_nonneg _)
  have hparseval : ∑ t : ZMod N, ‖fourier g t‖ ^ 2 ≤ (N : Real) * S.card := by
    rw [identity_2_3_holds]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    have heq : (∑ s : ZMod N, ‖g s‖ ^ 2) = ∑ s ∈ S, ‖f s‖ ^ 2 := by
      simp only [g, restrictToCell, apply_ite, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0)]
      rw [← Finset.sum_filter]
      simp
    rw [heq]
    calc
      _ ≤ ∑ _s ∈ S, (1 : Real) := Finset.sum_le_sum fun s _ ↦
        pow_le_one₀ (norm_nonneg _) (hf s)
      _ = _ := by simp
  have hfour : ∑ t : ZMod N, ‖fourier g t‖ ^ 4 ≤
      (N : Real) * ((S.card : Real) ^ 2 * ‖fourier g r‖) := by
    calc
      _ = ∑ t : ZMod N, ‖fourier g t‖ ^ 2 * ‖fourier g t‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ ≤ ∑ t : ZMod N, (‖fourier g r‖ * S.card) * ‖fourier g t‖ ^ 2 :=
        Finset.sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_right (hpoint t) (sq_nonneg _)
      _ = (‖fourier g r‖ * S.card) * ∑ t : ZMod N, ‖fourier g t‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (‖fourier g r‖ * S.card) * ((N : Real) * S.card) :=
        mul_le_mul_of_nonneg_left hparseval (by positivity)
      _ = _ := by ring
  rw [fourthMoment_eq_degreeOneEnergy] at hfour
  refine ⟨r, ?_⟩
  exact (mul_le_mul_iff_right₀ (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).mp hfour

/-- Partition nonuniformity of degree one gives total Fourier correlation
at least beta times the ambient size. No prime-model or selected-cell loss
is needed: every cell supplies its own frequency. -/
theorem partition_linear_nonuniformity_fourier_bias {N K m : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin K → ModAP N) (beta : Real)
    (hf : DiscValued f) (hβ : 0 ≤ beta) (hm : 0 < m)
    (hpart : IsPartition (fun i ↦ (Q i).carrier) Finset.univ)
    (hsize : ∀ i, (Q i).carrier.card ≤ m)
    (hfail : ¬ UniformOnPartition f 1 beta Q m) :
    ∃ r : Fin K → ZMod N,
      beta * N < ∑ i, ‖∑ x ∈ (Q i).carrier, f x * exponential (-(r i * x))‖ := by
  classical
  have henergy : beta * (m : Real) ^ 3 * K <
      ∑ i, ∑ a : Point N 1, ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2 := by
    unfold UniformOnPartition at hfail
    simp only [sum_cube_succ_eq_sum_norm_sq, Complex.ofReal_re, Nat.reduceAdd] at hfail
    exact lt_of_not_ge hfail
  choose r hr using fun i ↦ exists_fourier_restrict_energy_bound (Q i).carrier f hf
  have hbound : (∑ i, ∑ a : Point N 1,
      ‖∑ s : ZMod N, cubeDifference (restrictToCell (Q i).carrier f) a s‖ ^ 2) ≤
      (m : Real) ^ 2 * ∑ i, ‖fourier (restrictToCell (Q i).carrier f) (r i)‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact (hr i).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsize i) 2) (norm_nonneg _))
  have htotal : N ≤ m * K := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin K))) ↦ hsize i)
    rw [hpart.sum_card] at h
    simpa [mul_comm] using h
  have htotalR : (N : Real) ≤ (m : Real) * K := by exact_mod_cast htotal
  have hstrict : beta * (m : Real) * K <
      ∑ i, ‖fourier (restrictToCell (Q i).carrier f) (r i)‖ := by
    apply (mul_lt_mul_iff_right₀ (show (0 : Real) < (m : Real) ^ 2 by positivity)).mp
    calc
      (m : Real) ^ 2 * (beta * m * K) = beta * (m : Real) ^ 3 * K := by ring
      _ < _ := henergy.trans_le hbound
  refine ⟨r, ?_⟩
  simp_rw [← fourier_restrictToCell]
  exact (by nlinarith only [mul_le_mul_of_nonneg_left htotalR hβ] : beta * N ≤ beta * (m : Real) * K).trans_lt hstrict

end LeanProofs.GowersSzemeredi
