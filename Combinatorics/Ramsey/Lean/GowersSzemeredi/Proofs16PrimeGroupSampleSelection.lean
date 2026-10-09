import GowersSzemeredi.Proofs16SampleMeanSelection

/-! The finite prime-cyclic sampling step behind Claim 6.3. One sample
retains many indices, has all Boolean subsums distinct, and hits the sparse
kernel sets of only a prescribed small number of tuples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem booleanSampleImage_card_of_injective {N r : Nat} [NeZero N]
    (e : Fin r → ZMod N) (he : Function.Injective (booleanSampleValue e)) :
    (Finset.univ.image (booleanSampleValue e)).card = 2^r := by
  rw [Finset.card_image_of_injective _ he]
  simp

/-- Retained density is independent of `epsilon`; only the sparse-kernel
budget changes with the allowed exceptional-tuple fraction. -/
theorem prime_group_sample_selection {N r m : Nat} [NeZero N] [Fact N.Prime]
    (hr : 0 < r) (X : Finset (ZMod N)) (B : ZMod N → Finset (ZMod N))
    {I : Type*} (Q : Finset I) (Z : I → Finset (ZMod N))
    {b beta eta epsilon : Real} (hb : 0 < b) (hbeta : 0 < beta) (heta : 0 ≤ eta) (he : 0 < epsilon)
    (hX : b*N ≤ (X.card : Real)) (hB : ∀ x ∈ X, beta*N ≤ ((B x).card : Real))
    (hQ : (Q.card : Real) ≤ (N : Real)^m)
    (hZ : ∀ q ∈ Q, ((Z q).card : Real) ≤ eta*N)
    (hbadBudget : 8*(3 : Real)^r*eta ≤ epsilon*b*beta^r)
    (hcollisionBudget : 8*(3 : Real)^r ≤ b*beta^r*N) :
    ∃ e : Fin r → ZMod N, Function.Injective (booleanSampleValue e) ∧
      (Finset.univ.image (booleanSampleValue e)).card = 2^r ∧
      b*beta^r*N/2 ≤ ((retainedSampleIndices X B e).card : Real) ∧
      ((sampleBadIndices Q Z e).card : Real) ≤ epsilon*(N : Real)^m/2 := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcardE : Fintype.card (Fin r → ZMod N) = N^r := by simp
  have hbound : ∀ e : Fin r → ZMod N, (retainedSampleIndices X B e).card ≤ N := by
    intro e
    exact (Finset.card_filter_le _ _).trans (by simpa using Finset.card_le_univ X)
  have hret : (b*beta^r)*N*Fintype.card (Fin r → ZMod N) ≤
      ∑ e : Fin r → ZMod N, ((retainedSampleIndices X B e).card : Real) := by
    rw [hcardE, Nat.cast_pow]
    calc
      (b*beta^r)*N*(N : Real)^r = beta^r*(N : Real)^r*(b*N) := by ring
      _ ≤ beta^r*(N : Real)^r*X.card := mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ _ := sample_retention_sum_ge X B hbeta.le hB
  have hbad : ∑ e : Fin r → ZMod N, ((sampleBadIndices Q Z e).card : Real) ≤
      ((3 : Real)^r*eta)*(N^m : Nat)*Fintype.card (Fin r → ZMod N) := by
    rw [hcardE, Nat.cast_pow, Nat.cast_pow]
    calc
      _ ≤ (3 : Real)^r*eta*(N : Real)^r*Q.card := sample_bad_indices_sum_le hr Q Z hZ
      _ ≤ (3 : Real)^r*eta*(N : Real)^r*(N : Real)^m :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
      _ = _ := by ring
  have hpow : (N : Real)^(r-1)*N = (N : Real)^r := by
    rw [←pow_succ]
    congr 1
    omega
  have hcollision : ((Finset.univ.filter fun e : Fin r → ZMod N =>
      ¬ Function.Injective (booleanSampleValue e)).card : Real) ≤
        ((3 : Real)^r/N)*Fintype.card (Fin r → ZMod N) := by
    rw [hcardE, Nat.cast_pow, ←hpow]
    have hc : ((Finset.univ.filter fun e : Fin r → ZMod N =>
        ¬ Function.Injective (booleanSampleValue e)).card : Real) ≤ (3 : Real)^r*(N : Real)^(r-1) := by
      exact_mod_cast (boolean_sample_collisions_card_le (N := N) (r := r))
    convert hc using 1
    field_simp
  have hbadBudget' : 2*((3 : Real)^r*eta)/epsilon ≤ (b*beta^r)/4 := by
    rw [div_le_iff₀ he]
    nlinarith
  have hcollisionBudget' : 2*((3 : Real)^r/N) ≤ (b*beta^r)/4 := by
    rw [show 2*((3 : Real)^r/N) = (2*(3 : Real)^r)/N by ring, div_le_iff₀ hn]
    nlinarith
  obtain ⟨e, hc, hretained, hsmall⟩ := exists_sample_of_mean_bounds N (N^m) (NeZero.pos N)
    (pow_pos (NeZero.pos N) m) (fun e => (retainedSampleIndices X B e).card)
    (fun e => (sampleBadIndices Q Z e).card) (fun e => ¬ Function.Injective (booleanSampleValue e))
    (mul_pos hb (pow_pos hbeta r)) he hbound hret hbad (by
      convert hcollision using 1
      congr 2
      ext e
      simp only [Finset.mem_filter]) hbadBudget' hcollisionBudget' 
  have hinj : Function.Injective (booleanSampleValue e) := not_not.mp hc
  refine ⟨e, hinj, booleanSampleImage_card_of_injective e hinj, ?_, ?_⟩
  · simpa only [div_mul_eq_mul_div] using hretained
  · simpa only [Nat.cast_pow, div_mul_eq_mul_div] using hsmall

end LeanProofs.GowersSzemeredi
