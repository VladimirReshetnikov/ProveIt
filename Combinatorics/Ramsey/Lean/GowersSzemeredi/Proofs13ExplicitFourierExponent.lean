import GowersSzemeredi.Proofs13PrintedExponentComparison

/-! A conventional explicit tower bound supported by the complete extraction.
The original printed target is preserved separately in the catalogue. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A simple exponential majorant, used to absorb polynomial prefactors. -/
theorem le_two_rpow_two_mul {x : Real} (hx : 0 ≤ x) : x ≤ (2 : Real) ^ (2 * x) := by
  have hlog : (1 : Real) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlin := Real.add_one_le_exp (Real.log 2 * (2 * x))
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith only [hlog, hlin, hx]

/-- The enormous spectral parameter absorbs the polynomial and fixed
prefactors in the checked square exponent. -/
theorem section13SquareExponent_ge_spectral_power {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (2 : Real) ^ (-(15 * section13Q delta)) ≤ section13SquareExponent delta := by
  let Q := section13Q delta
  have hC : (3712 : Real) ≤ (2 : Real) ^ ((2 : Nat) ^ 20) := by
    calc
      _ ≤ (2 : Real) ^ (12 : Nat) := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hpower : delta⁻¹ ≤ delta ^ (-((2 : Real) ^ 21)) := by
    calc
      _ = delta ^ (-(1 : Real)) := (Real.rpow_neg_one delta).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδone (by norm_num)
  have hQinv : 3712 * delta⁻¹ ≤ Q :=
    mul_le_mul hC hpower (inv_nonneg.mpr hδ.le) (by positivity)
  have hinv : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr hδone
  have hQ386 : 386 ≤ Q := by nlinarith only [hQinv, hinv]
  have hδpow : delta ^ 1856 ≥ (2 : Real) ^ (-Q) := by
    have hgrow := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le)
      (le_two_rpow_two_mul (inv_nonneg.mpr hδ.le)) 1856
    have hexp : ((2 : Real) ^ (2 * delta⁻¹)) ^ 1856 = (2 : Real) ^ (3712 * delta⁻¹) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    rw [hexp] at hgrow
    have hupper : (delta ^ 1856)⁻¹ ≤ (2 : Real) ^ Q := by
      simpa only [inv_pow] using hgrow.trans
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hQinv)
    have hi := inv_anti₀ (inv_pos.mpr (pow_pos hδ 1856)) hupper
    simpa only [inv_inv, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)] using hi
  have hconst : (2 : Real) ^ (-Q) ≤ (2 : Real) ^ (-(386 : Int)) := by
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    linarith only [hQ386]
  rw [section13SquareExponent_formula]
  calc
    _ = ((2 : Real) ^ (-Q) * (2 : Real) ^ (-Q)) / (2 : Real) ^ (13 * Q) := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_sub (by norm_num)]
      congr 1
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hconst hδpow (Real.rpow_nonneg (by norm_num) _) (by positivity))
      (Real.rpow_nonneg (by norm_num) _)

/-- After the Fourier-density substitution, a power with exponent 2^88
absorbs both the spectral constant and the preceding factor fifteen. -/
theorem section13_fourier_spectral_upper {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    15 * section13Q ((alpha / 2) ^ ((2 : Nat) ^ 66)) ≤
      (2 / alpha) ^ ((2 : Nat) ^ 88) := by
  let t := 2 / alpha
  have ht : 2 ≤ t := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have htpos : 0 < t := (by norm_num : (0 : Real) < 2).trans_le ht
  have ha : 0 < alpha / 2 := by positivity
  have hinv : (alpha / 2)⁻¹ = t := by dsimp [t]; field_simp
  have hcollapse : ((alpha / 2) ^ ((2 : Nat) ^ 66)) ^ (-((2 : Real) ^ 21)) =
      t ^ ((2 : Nat) ^ 87) := by
    rw [← Real.rpow_natCast (alpha / 2) ((2 : Nat) ^ 66), ← Real.rpow_mul ha.le]
    rw [show (((2 : Nat) ^ 66 : Nat) : Real) * (-((2 : Real) ^ 21)) =
      -((((2 : Nat) ^ 87 : Nat) : Real)) by norm_num]
    rw [Real.rpow_neg_eq_inv_rpow, hinv, Real.rpow_natCast]
  have hc : 15 * (2 : Real) ^ ((2 : Nat) ^ 20) ≤ t ^ ((2 : Nat) ^ 87) := by
    calc
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ 20) * (2 : Real) ^ (4 : Nat) := by
        have hh : (15 : Real) ≤ (2 : Real) ^ (4 : Nat) := by norm_num
        exact (mul_le_mul_of_nonneg_right hh
          (pow_nonneg (by norm_num : (0 : Real) ≤ 2) ((2 : Nat) ^ 20))).trans_eq (mul_comm _ _)
      _ = (2 : Real) ^ ((2 : Nat) ^ 20 + 4) := (pow_add _ _ _).symm
      _ ≤ (2 : Real) ^ ((2 : Nat) ^ 87) := pow_le_pow_right₀ (by norm_num) (by norm_num)
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) ht _
  unfold section13Q
  rw [hcollapse]
  calc
    _ = (15 * (2 : Real) ^ ((2 : Nat) ^ 20)) * t ^ ((2 : Nat) ^ 87) := (mul_assoc _ _ _).symm
    _ ≤ t ^ ((2 : Nat) ^ 87) * t ^ ((2 : Nat) ^ 87) :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg htpos.le _)
    _ = t ^ ((2 : Nat) ^ 88) := by rw [← pow_add]; congr 1

/-- A fully explicit conventional tower exponent supported by the checked
Fourier square construction. -/
theorem section13_fourier_exponent_lower {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ≤
      section13SquareExponent ((alpha / 2) ^ ((2 : Nat) ^ 66)) := by
  have hδ : 0 < (alpha / 2) ^ ((2 : Nat) ^ 66) := pow_pos (by positivity) _
  have hδone : (alpha / 2) ^ ((2 : Nat) ^ 66) ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hαone])
  calc
    _ = (2 : Real) ^ (-((2 / alpha) ^ ((2 : Nat) ^ 88))) := by
      rw [Real.rpow_neg_eq_inv_rpow, one_div]
    _ ≤ (2 : Real) ^ (-(15 * section13Q ((alpha / 2) ^ ((2 : Nat) ^ 66)))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg (section13_fourier_spectral_upper hα hαone))
    _ ≤ _ := section13SquareExponent_ge_spectral_power hδ hδone

/-- A fully proved explicit-bound version of the weak bilinear Fourier
 theorem. The catalogue's stronger printed length remains a separate goal. -/
theorem theorem_13_12_with_explicit_bound :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
        ∃ P Q : ModAP N, ∃ B : Finset (Pair N), ∃ phi : Pair N → ZMod N,
          P.step != 0 ∧ P.step = Q.step ∧ P.IsProper ∧ Q.IsProper ∧ P.length = Q.length ∧
          (N : Real) ^ ((1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88))) ≤ P.length ∧
          B ⊆ P.carrier.product Q.carrier ∧
          (alpha / 2) ^ ((2 : Nat) ^ 76) * P.length * Q.length ≤ B.card ∧
          BilinearOn (P.carrier.product Q.carrier) phi ∧
          ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := theorem_13_12_with_extraction_exponent alpha hα hαone
  refine ⟨N₀, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, hsize, hbox, hmass, hbil, hfourier⟩ :=
    hN₀ N hN f hf hnot
  refine ⟨P, Q, B, phi, hs, hs', hP, hQ, hlen, ?_, hbox, hmass, hbil, hfourier⟩
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast NeZero.pos N
  exact (Real.rpow_le_rpow_of_exponent_le hNreal (section13_fourier_exponent_lower hα hαone)).trans hsize

end LeanProofs.GowersSzemeredi
