import GowersSzemeredi.Proofs18AffineCubeEnergy
import GowersSzemeredi.Proofs16BaseCaseLongBoxTransport
import Mathlib.NumberTheory.Bertrand

/-! A comparable prime model for a local uniformity obstruction. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Interval extension of a bounded index function remains disc-valued. -/
theorem intervalExtension_discValued {L : Nat} (N : Nat) {g : Fin L → Complex}
    (hg : DiscValued g) : DiscValued (intervalExtension N g) := by
  intro x
  by_cases hx : x.val < L
  · simpa only [intervalExtension, dif_pos hx] using hg ⟨x.val, hx⟩
  · simp only [intervalExtension, dif_neg hx, norm_zero, zero_le_one]

/-- Local normalization cancels the old modulus exactly on transfer. -/
theorem ModAP.restrict_uniform_iff_local_scale {N M k : Nat} [Fact N.Prime] [NeZero M]
    (P : ModAP N) (f : ZMod N → Complex) (hd : P.step ≠ 0)
    (hN : (k + 2) * P.length ≤ N) (hM : (k + 2) * P.length ≤ M)
    (beta r : Real) :
    UniformOfDegree (restrictToCell P.carrier f) (beta * (r / N) ^ (k + 2)) k ↔
      UniformOfDegree (intervalExtension M (P.pullbackFunction f))
        (beta * (r / M) ^ (k + 2)) k := by
  have hNne : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hMne : (M : Real) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hscale : (beta * (r / N) ^ (k + 2)) * ((N : Real) / M) ^ (k + 2) =
      beta * (r / M) ^ (k + 2) := by
    rw [mul_assoc, ← mul_pow]
    congr 2
    field_simp
  simpa only [hscale] using P.restrict_uniform_iff f hd hN hM (beta * (r / N) ^ (k + 2))

/-- A local obstruction on a sufficiently short proper progression transfers
to a prime modulus between (k+2)*L and twice that scale. Its surviving
uniformity parameter depends on beta and k, not on the old modulus. -/
theorem ModAP.exists_prime_model_of_nonuniform {N k : Nat} [Fact N.Prime]
    (P : ModAP N) (f : ZMod N → Complex) (beta r : Real)
    (hP : P.IsProper) (hL : 2 ≤ P.length) (hN : (k + 2) * P.length ≤ N)
    (hf : DiscValued f) (hβ : 0 ≤ beta) (hr : (P.length : Real) ≤ r)
    (hnot : ¬ UniformOfDegree (restrictToCell P.carrier f) (beta * (r / N) ^ (k + 2)) k) :
    ∃ M : Nat, ∃ hM : M.Prime,
      letI : NeZero M := ⟨hM.ne_zero⟩
      (k + 2) * P.length < M ∧ M ≤ 2 * ((k + 2) * P.length) ∧
      DiscValued (intervalExtension M (P.pullbackFunction f)) ∧
      ¬ UniformOfDegree (intervalExtension M (P.pullbackFunction f))
        (beta / (2 * (k + 2 : Nat) : Real) ^ (k + 2)) k := by
  have hn : (k + 2) * P.length ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  obtain ⟨M, hM, hMlower, hMupper⟩ := Nat.exists_prime_lt_and_le_two_mul ((k + 2) * P.length) hn
  letI : NeZero M := ⟨hM.ne_zero⟩
  have hd := BaseCase.proper_modAP_step_ne_zero_of_two_le P hP hL
  have hnew : ¬ UniformOfDegree (intervalExtension M (P.pullbackFunction f))
      (beta * (r / M) ^ (k + 2)) k := by
    rwa [P.restrict_uniform_iff_local_scale f hd hN hMlower.le beta r] at hnot
  have hMpos : (0 : Real) < M := by exact_mod_cast hM.pos
  have hden : (0 : Real) < 2 * (k + 2 : Nat) := by positivity
  have hratio : (1 : Real) / (2 * (k + 2 : Nat)) ≤ r / M := by
    apply (div_le_div_iff₀ hden hMpos).mpr
    have hMreal : (M : Real) ≤ 2 * (k + 2 : Nat) * P.length := by
      exact_mod_cast (by simpa only [mul_assoc] using hMupper : M ≤ 2 * (k + 2) * P.length)
    have hmul := mul_le_mul_of_nonneg_left hr hden.le
    nlinarith only [hMreal, hmul]
  have hparam : beta / (2 * (k + 2 : Nat) : Real) ^ (k + 2) ≤ beta * (r / M) ^ (k + 2) := by
    calc
      _ = beta * ((1 : Real) / (2 * (k + 2 : Nat))) ^ (k + 2) := by rw [div_pow, one_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _) hβ
  refine ⟨M, hM, hMlower, hMupper, intervalExtension_discValued M (fun i => hf (P.index i)), ?_⟩
  intro huniform
  apply hnew
  exact huniform.trans (mul_le_mul_of_nonneg_right hparam (pow_nonneg hMpos.le _))

end LeanProofs.GowersSzemeredi
