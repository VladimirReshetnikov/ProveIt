import GowersSzemeredi.Proofs18FunctionDiscrepancyReduction
import GowersSzemeredi.Proofs18GeneralIntervalStopping
import GowersSzemeredi.Proofs18NaturalReindex
import GowersSzemeredi.Proofs18DensityIteration
import Mathlib.NumberTheory.Bertrand

/-! General prime-free density iteration from an explicit function discrepancy
bound. Constants are fixed at the initial density and remain unchanged as
the actual density increases. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def intervalDiscrepancyStepThreshold (k : Nat) (delta beta T : Real) : Real :=
  max (k : Real) (max T (max (32 / beta) ((512 * (k : Real) ^ 2 + 1) / delta ^ k)))

/-- Combine relative-uniform stopping, the nonuniform interval increment,
a comparable prime, and progression reindexing into the exact iteration
interface. The discrepancy hypothesis retains its explicit threshold. -/
theorem FunctionDiscrepancyBound.interval_density_step
    {k : Nat} {delta tau sigma T : Real} (hk : 2 ≤ k) (hδ : 0 < delta)
    (hτ : 0 < tau) (hσ : 0 < sigma)
    (hbound : FunctionDiscrepancyBound (k - 2) (intervalUniformityParameter delta k) tau sigma T) :
    IntervalDensityStep k delta (tau / 8)
      (tau / (8 * boundaryRefinementConstant (tau / 64))) (sigma / 16)
      (intervalDiscrepancyStepThreshold k delta tau T) := by
  classical
  intro L hL B d hd hcard
  let alpha := intervalUniformityParameter delta k
  have hα : 0 < alpha := intervalUniformityParameter_pos hδ (by omega : 0 < k)
  obtain ⟨hkLr, hexp, hscale, hlarge⟩ : (k : Real) ≤ L ∧
      T ≤ L ∧ 32 / tau ≤ L ∧ (512 * (k : Real) ^ 2 + 1) / delta ^ k ≤ L := by
    simpa only [intervalDiscrepancyStepThreshold, max_le_iff] using hL
  have hkL : k ≤ L := by exact_mod_cast hkLr
  have hLpos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
  have hC : 0 < boundaryRefinementConstant (tau / 64) := section5LocalRefinementConstant_pos _ _
  obtain ⟨N, hNprime, hNlower, hNupper⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * L) (by omega)
  letI : NeZero N := ⟨hNprime.ne_zero⟩
  letI : Fact N.Prime := ⟨hNprime⟩
  have hLN : (L : Real) ≤ N := by exact_mod_cast (by omega : L ≤ N)
  let D : Real := B.card / (L : Real)
  have hDcard : (B.card : Real) = D * L := by dsimp [D]; field_simp
  have hdD : d ≤ D := (le_div_iff₀ hLpos).mpr hcard
  have hδD : delta ≤ D := hd.trans hdD
  have hDone : D ≤ 1 := by
    apply (div_le_one hLpos).mpr
    exact_mod_cast (show B.card ≤ L by simpa using Finset.card_le_univ B)
  have hDpow : delta ^ k ≤ D ^ k := pow_le_pow_left₀ hδ.le hδD k
  by_cases hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B D)) alpha (k - 2)
  · left
    apply interval_relative_uniform_hasNatAP hk hNlower hkL (by omega) B D alpha
      (hδ.le.trans hδD) hDone hα.le
    · exact (intervalUniformityParameter_count_error hδ.le (by omega : 0 < k)).le.trans
        (div_le_div_of_nonneg_right hDpow (by positivity))
    · have hb := (div_le_iff₀ (pow_pos hδ k)).mp hlarge
      have hm := mul_le_mul hDpow hLN (Nat.cast_nonneg _) (pow_nonneg (hδ.le.trans hδD) k)
      nlinarith
    · exact hu
  · right
    have hscaleN : 32 ≤ tau * N := by
      have hs := (div_le_iff₀ hτ).mp hscale
      have hm := mul_le_mul_of_nonneg_left hLN hτ.le
      nlinarith
    obtain ⟨Q, hQ, _, hsize, hinc⟩ := hbound.natural_interval_increment
      hτ N L hNlower (hexp.trans hLN) hscaleN B D
      (hδ.le.trans hδD) hDone hDcard hu
    refine ⟨Q.length, Q.pullback (B.image Fin.val), ?_, ?_, Q.hasNatAP_of_pullback hQ _⟩
    · apply le_trans _ hsize
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hLN (by positivity : 0 ≤ sigma / 16))
        (by positivity : 0 ≤ tau / (8 * boundaryRefinementConstant (tau / 64)))
    · rw [Q.card_pullback hQ]
      apply le_trans _ hinc
      exact mul_le_mul_of_nonneg_right (by change d + tau / 8 ≤ D + tau / 8; linarith) (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
