import GowersSzemeredi.Proofs13UniformDensityRecurrence
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Finite recurrence thresholds, uniform over the actual density and every
admissible spectrum size. No eventual-growth witness enters the definitions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section13RecurrenceLengthThreshold (alpha : Real) (q : Nat) : Real :=
  max (simultaneousPolynomialThreshold 2 q + 1 : Nat)
    (max (positivePowerThreshold 8 1 ((1 : Real) / (2 : Real) ^ (12 * q)))
      (positivePowerThreshold (160 + 2 * alpha ^ 32) (alpha ^ 32)
        ((1 : Real) / (2 : Real) ^ (12 * q))))

theorem section13_recurrence_scale_of_explicit_length {alpha : Real} (hα : 0 < alpha)
    (q L : Nat) (hL : section13RecurrenceLengthThreshold alpha q ≤ L) :
    Section13RecurrenceScale alpha q L := by
  have he : (0 : Real) < (1 : Real) / (2 : Real) ^ (12 * q) := by positivity
  have hfirst : (simultaneousPolynomialThreshold 2 q + 1 : Nat) ≤ L := by
    exact_mod_cast ((le_max_left _ _).trans hL : ((simultaneousPolynomialThreshold 2 q + 1 : Nat) : Real) ≤ L)
  refine ⟨by omega, ?_, ?_⟩
  · have hs := positivePowerThreshold_spec (C := 8) zero_lt_one he
      ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
    simpa only [one_mul] using hs
  · exact positivePowerThreshold_spec (pow_pos hα _) he
      ((le_max_right _ _).trans ((le_max_right _ _).trans hL))

def section13InitialRecurrenceThreshold (delta : Real) (q : Nat) : Real :=
  positivePowerThreshold (section13RecurrenceLengthThreshold delta q + 2)
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi))
    (section13ThetaOne (section10Lambda (delta ^ 32 / 16)) ^ 2 / (16 * (q : Real)))

/-- A single displayed threshold for fixed q handles every larger actual
density and both permitted initial rounding cases. -/
theorem section13_density_recurrence_scale_explicit {delta : Real}
    (hδ : 0 < delta) {q N : Nat} (hq : 0 < q)
    (hN : section13InitialRecurrenceThreshold delta q ≤ N)
    (alpha : Real) (hδα : delta ≤ alpha) (p L : Nat)
    (hp : IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
      (64 * Real.pi) * (N : Real) ^
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p)
    (hL : L = p ∨ L + 1 = p) : Section13RecurrenceScale alpha q L := by
  let theta := section10Lambda (delta ^ 32 / 16)
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hθ₁ : 0 < section13ThetaOne theta := by unfold section13ThetaOne; positivity
  have hd : 0 < section13ThetaOne theta / (64 * Real.pi) := by positivity
  have hu : 0 < section13ThetaOne theta ^ 2 / (16 * (q : Real)) := by positivity
  have hNreal : (1 : Real) ≤ N := (positivePowerThreshold_one_le _ _ _).trans hN
  have hbase := positivePowerThreshold_spec hd hu hN
  have ht := section13ThetaOne_mono hθ.le (section13_cutoff_mono hδ hδα)
  have hdle := div_le_div_of_nonneg_right ht (by positivity : (0 : Real) ≤ 64 * Real.pi)
  have hule := div_le_div_of_nonneg_right (pow_le_pow_left₀ hθ₁.le ht 2)
    (by positivity : (0 : Real) ≤ 16 * q)
  have hx : section13RecurrenceLengthThreshold delta q + 2 ≤
      section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) / (64 * Real.pi) *
        (N : Real) ^ (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 /
          (16 * (q : Real))) :=
    hbase.trans (mul_le_mul hdle (Real.rpow_le_rpow_of_exponent_le hNreal hule)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) (hd.le.trans hdle))
  have hLL : section13RecurrenceLengthThreshold delta q ≤ L := by
    have hupp := hp.2
    rcases hL with hL | hL
    · subst L
      linarith only [hupp, hx]
    · have hLc : (L : Real) + 1 = p := by exact_mod_cast hL
      linarith only [hupp, hx, hLc]
  exact section13_recurrence_scale_density_mono hδ hδα
    (section13_recurrence_scale_of_explicit_length hδ q L hLL)

/-- Explicit finite maximum over the permitted spectrum sizes. -/
def section13DensityRecurrenceThreshold (delta : Real) : Nat :=
  max 3 ((Finset.range (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1)).sup
    (fun q => Nat.ceil (section13InitialRecurrenceThreshold delta q)))

theorem section13_uniform_density_recurrence_scale_explicit {delta : Real} (hδ : 0 < delta)
    (N : Nat) (hN : section13DensityRecurrenceThreshold delta ≤ N)
    (alpha : Real) (hδα : delta ≤ alpha) (q p L : Nat) (hq : 0 < q)
    (hqB : (q : Real) ≤ section13QBound (section10Lambda (alpha ^ 32 / 16)))
    (hp : IsNatFloor (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) /
      (64 * Real.pi) * (N : Real) ^
        (section13ThetaOne (section10Lambda (alpha ^ 32 / 16)) ^ 2 / (16 * (q : Real)))) p)
    (hL : L = p ∨ L + 1 = p) : Section13RecurrenceScale alpha q L := by
  have hθ : 0 < section10Lambda (delta ^ 32 / 16) := by unfold section10Lambda; positivity
  have hqfloor : q ≤ Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) :=
    Nat.le_floor (hqB.trans (section13QBound_antitone hθ (section13_cutoff_mono hδ hδα)))
  have hqmem : q ∈ Finset.range (Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) + 1) :=
    Finset.mem_range.mpr (by omega)
  have hceil : Nat.ceil (section13InitialRecurrenceThreshold delta q) ≤ N :=
    (Finset.le_sup hqmem).trans ((le_max_right _ _).trans hN)
  exact section13_density_recurrence_scale_explicit hδ hq
    ((Nat.le_ceil _).trans (by exact_mod_cast hceil)) alpha hδα p L hp hL

/-- Stage 13.5 now has a closed density-uniform starting modulus. -/
theorem lemma_13_5_uniform_density_explicit {delta : Real} (hδ : 0 < delta)
    (N : Nat) [Fact N.Prime] (S : Section13Context N) (D : Stage134Data N)
    (hS : delta ≤ S.alpha) (hN : section13DensityRecurrenceThreshold delta ≤ N)
    (h134 : IsStage134Data S (section10Lambda (S.alpha ^ 32 / 16)) D) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  have hs := section13_uniform_density_recurrence_scale_explicit hδ N hN S.alpha hS D.q D.m D.P.length
    h134.1 h134.2.2.2.2.1 h134.2.2.2.2.2.1 h134.2.2.2.2.2.2.1
  have hNthree : 3 ≤ N := (le_max_left _ _).trans hN
  exact lemma_13_5_with_scale (Fact.out : N.Prime) (bne_iff_ne.mpr (by omega))
    S D (section10Lambda (S.alpha ^ 32 / 16)) h134 hs.1 hs.2.1 hs.2.2

end LeanProofs.GowersSzemeredi
