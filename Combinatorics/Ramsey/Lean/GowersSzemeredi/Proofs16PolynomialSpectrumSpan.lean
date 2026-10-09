import GowersSzemeredi.Proofs16BohrSpectrumBudget

/-! A modulus-independent polynomial cutoff for the large spectrum of a
Bohr set. The finite-size hypothesis pays for the endpoints of the
frequency bands; all rounding errors are retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Increasing the coefficient cutoff enlarges the bounded frequency span. -/
theorem boundedFrequencySpan_mono {N : Nat} [NeZero N] {ι : Type*} [Fintype ι]
    (gamma : ι → ZMod N) {R S : Nat} (hRS : R ≤ S) :
    boundedFrequencySpan gamma R ⊆ boundedFrequencySpan gamma S := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  let w : ι → centeredBall N S := fun i => ⟨v i, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ((Finset.mem_filter.mp (v i).property).2).trans hRS⟩⟩
  exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩

/-- The nonnegative half of a non-wrapping centered interval has c+1 points. -/
theorem centeredBall_card_ge_succ {N : Nat} [NeZero N] {c : Nat} (hc : 2 * c < N) :
    c + 1 ≤ (centeredBall N c).card := by
  have h : (Finset.range (c + 1)).card ≤ (centeredBall N c).card := by
    apply Finset.card_le_card_of_injOn (fun i : Nat => (i : ZMod N))
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hval := ZMod.valMinAbs_natCast_of_le_half (n := N) (a := i) (by omega)
      simpa [centeredAbs, hval] using (show i ≤ c by omega)
    · intro i hi j hj hij
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      rw [ZMod.natCast_eq_natCast_iff'] at hij
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hij
  simpa using h

/-- Bohr membership is unchanged by rounding its radius down to a grid point. -/
theorem bohr_floor_radius {N : Nat} [NeZero N] (K : Finset (ZMod N)) {rho : Real}
    (hrho : 0 ≤ rho) : bohr K ((⌊rho * N⌋₊ : Real) / N) = bohr K rho := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  ext x
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall₂_congr
  intro r hr
  rw [div_mul_cancel₀ _ hN.ne']
  have hnonneg : 0 ≤ rho * N := mul_nonneg hrho hN.le
  rw [Nat.cast_le (α := Real), Nat.le_floor_iff hnonneg]

/-- A polynomial cutoff, independent of the modulus, contains all Fourier
coefficients of a Bohr indicator of normalized magnitude at least epsilon. -/
theorem large_bohr_fourier_mem_polynomial_boundedSpan {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) {rho epsilon : Real}
    (hrho : 0 < rho) (hrhoHalf : rho < 1 / 2)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hN : 8 * (K.card + 1 : Real) / epsilon ≤ (N : Real))
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier (indicator (bohr K rho)) xi‖) :
    xi ∈ boundedFrequencySpan (fun gamma : K => (gamma : ZMod N))
      ⌈max (8 * (K.card + 1 : Real) / (epsilon * rho))
        (128 * (K.card + 1 : Real)^2 / epsilon^2)⌉₊ := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let k : Real := K.card + 1
  have hk : 0 < k := by dsimp [k]; positivity
  let sigma : Real := min rho (epsilon / (16 * k))
  have hsigma : 0 < sigma := lt_min hrho (div_pos heps (by positivity))
  have hsrho : sigma ≤ rho := min_le_left _ _
  have hseps : sigma ≤ epsilon / (16 * k) := min_le_right _ _
  let a := ⌊rho * N⌋₊
  let c := ⌊sigma * N⌋₊
  have haR : (a : Real) ≤ rho * N := Nat.floor_le (by positivity)
  have hcR : (c : Real) ≤ sigma * N := Nat.floor_le (by positivity)
  have hca : c ≤ a := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hsrho hNR.le)
  have ha : 2 * a < N := by
    have := mul_lt_mul_of_pos_right hrhoHalf hNR
    have hreal : (2 : Real) * a < N := by linarith
    exact_mod_cast hreal
  have hc : 2 * c < N := by omega
  have hband : K.card * (4 * (c : Real) + 2) ≤ epsilon / 2 * N := by
    have hwidth : 16 * k * sigma ≤ epsilon := by
      have h := (le_div_iff₀ (show 0 < 16 * k by positivity)).mp hseps
      nlinarith only [h]
    have hscale := mul_le_mul_of_nonneg_right hwidth hNR.le
    have hfloor := mul_le_mul_of_nonneg_left hcR (show 0 ≤ 16 * k by positivity)
    have hsize : 8 * k ≤ N * epsilon := (div_le_iff₀ heps).mp hN
    have hknonneg : (0 : Real) ≤ K.card := Nat.cast_nonneg _
    have hcnonneg : (0 : Real) ≤ c := Nat.cast_nonneg _
    dsimp only [k] at hscale hfloor hsize
    nlinarith only [hscale, hfloor, hsize, hcnonneg, hknonneg]
  have hlarge' : epsilon * N ≤ ‖fourier (indicator (bohr K ((a : Real) / N))) xi‖ := by
    simpa only [a, bohr_floor_radius K hrho.le] using hlarge
  have hmem := large_bohr_fourier_mem_explicit_boundedSpan K hca ha hc heps heps1 hband hlarge'
  apply boundedFrequencySpan_mono (fun gamma : K => (gamma : ZMod N)) _ hmem
  apply Nat.ceil_mono
  have hC : (0 : Real) < (centeredBall N c).card := by
    have := centeredBall_card_ge_succ hc
    exact_mod_cast (show 0 < (centeredBall N c).card by omega)
  have hmass : sigma * N ≤ (centeredBall N c).card := by
    have hf := Nat.lt_floor_add_one (sigma * N)
    have hc' : (c : Real) + 1 ≤ (centeredBall N c).card := by exact_mod_cast centeredBall_card_ge_succ hc
    change sigma * N < (c : Real) + 1 at hf
    linarith
  have hcut : 8 * k * N / (epsilon * (centeredBall N c).card) ≤ 8 * k / (epsilon * sigma) := by
    apply (div_le_div_iff₀ (mul_pos heps hC) (mul_pos heps hsigma)).mpr
    have := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 8 * k * epsilon by positivity)
    nlinarith only [this]
  apply hcut.trans
  change 8 * k / (epsilon * sigma) ≤ max (8 * k / (epsilon * rho)) (128 * k^2 / epsilon^2)
  rcases le_total rho (epsilon / (16 * k)) with h | h
  · rw [show sigma = rho from min_eq_left h]
    exact le_max_left _ _
  · rw [show sigma = epsilon / (16 * k) from min_eq_right h]
    have heq : 8 * k / (epsilon * (epsilon / (16 * k))) = 128 * k^2 / epsilon^2 := by field_simp; ring
    rw [heq]
    exact le_max_right _ _

end LeanProofs.GowersSzemeredi
