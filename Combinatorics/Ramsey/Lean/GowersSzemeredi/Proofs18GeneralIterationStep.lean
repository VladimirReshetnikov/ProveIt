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
  intro L hL B d hd hcard
  let alpha := intervalUniformityParameter delta k
  simp only [intervalDiscrepancyStepThreshold, max_le_iff] at hL
  obtain ⟨hkLr, hexp, hscale, hlarge⟩ := hL
  have hkL : k ≤ L := by exact_mod_cast hkLr
  have hLpos : (0 : Real) < L := Nat.cast_pos.mpr (by omega)
  have hC : 0 < boundaryRefinementConstant (tau / 64) := section5LocalRefinementConstant_pos _ _
  obtain ⟨N, hNprime, hNlower, hNupper⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * L) (by omega)
  letI : NeZero N := ⟨hNprime.ne_zero⟩
  letI : Fact N.Prime := ⟨hNprime⟩
  have hLN : (L : Real) ≤ N := by exact_mod_cast (by omega : L ≤ N)
  let D : Real := B.card / (L : Real)
  have hDcard : (B.card : Real) = D * L := (div_mul_cancel₀ _ hLpos.ne').symm
  have hdD : d ≤ D := (le_div_iff₀ hLpos).mpr hcard
  have hδD : delta ≤ D := hd.trans hdD
  have hDone : D ≤ 1 := (div_le_one hLpos).mpr <| by
    exact_mod_cast (show B.card ≤ L by simpa using Finset.card_le_univ B)
  have hDpow : delta ^ k ≤ D ^ k := pow_le_pow_left₀ hδ.le hδD k
  by_cases hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B D)) alpha (k - 2)
  · left
    refine interval_relative_uniform_hasNatAP hk hNlower hkL (by omega) B D alpha
      (hδ.le.trans hδD) hDone (intervalUniformityParameter_pos hδ (by omega)).le
      ((intervalUniformityParameter_count_error hδ.le (by omega)).le.trans
        (div_le_div_of_nonneg_right hDpow (by positivity))) ?_ hu
    linarith [(div_le_iff₀ (pow_pos hδ k)).mp hlarge,
      mul_le_mul hDpow hLN (Nat.cast_nonneg _) (pow_nonneg (hδ.le.trans hδD) k)]
  · right
    have hscaleN : 32 ≤ tau * N := by
      linarith [(div_le_iff₀ hτ).mp hscale, mul_le_mul_of_nonneg_left hLN hτ.le]
    obtain ⟨Q, hQ, _, hsize, hinc⟩ := hbound.natural_interval_increment hτ N L hNlower
      (hexp.trans hLN) hscaleN B D (hδ.le.trans hδD) hDone hDcard hu
    refine ⟨Q.length, Q.pullback (B.image Fin.val), le_trans (by gcongr) hsize, ?_,
      Q.hasNatAP_of_pullback hQ _⟩
    rw [Q.card_pullback hQ]
    exact le_trans (by gcongr) hinc

end LeanProofs.GowersSzemeredi
