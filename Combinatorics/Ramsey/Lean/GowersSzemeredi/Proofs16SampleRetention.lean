import GowersSzemeredi.Proofs16TernarySampleCollisions

/-! Exact finite averaging for the sampling step. Retention is counted by
product domains, while sparse-kernel tuple losses are counted by signed
subsums. The two estimates are independent of any probability library. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def retainedSampleIndices {N r : Nat} [NeZero N] (X : Finset (ZMod N))
    (B : ZMod N → Finset (ZMod N)) (e : Fin r → ZMod N) : Finset (ZMod N) :=
  X.filter fun x => ∀ i, e i ∈ B x

theorem sample_retention_sum_ge {N r : Nat} [NeZero N]
    (X : Finset (ZMod N)) (B : ZMod N → Finset (ZMod N)) {beta : Real}
    (hb : 0 ≤ beta) (hB : ∀ x ∈ X, beta*N ≤ ((B x).card : Real)) :
    beta^r*(N : Real)^r*X.card ≤
      ∑ e : Fin r → ZMod N, ((retainedSampleIndices X B e).card : Real) := by
  have hsum : ∑ e : Fin r → ZMod N, (retainedSampleIndices X B e).card =
      ∑ x ∈ X, (Finset.univ.filter fun e : Fin r → ZMod N => ∀ i, e i ∈ B x).card := by
    simp only [retainedSampleIndices, Finset.card_filter]
    exact Finset.sum_comm
  have hcard : ∀ x : ZMod N,
      (Finset.univ.filter fun e : Fin r → ZMod N => ∀ i, e i ∈ B x).card = (B x).card^r := by
    intro x
    have he : (Finset.univ.filter fun e : Fin r → ZMod N => ∀ i, e i ∈ B x) =
        Fintype.piFinset (fun _ : Fin r => B x) := by
      ext e
      simp [Fintype.mem_piFinset]
    rw [he, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsumR : ∑ e : Fin r → ZMod N, ((retainedSampleIndices X B e).card : Real) =
      ∑ x ∈ X, ((B x).card : Real)^r := by
    exact_mod_cast hsum.trans (Finset.sum_congr rfl (fun x _ => hcard x))
  rw [hsumR]
  calc
    beta^r*(N : Real)^r*X.card = ∑ _x ∈ X, (beta*N)^r := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_pow]; ring
    _ ≤ _ := Finset.sum_le_sum fun x hx => pow_le_pow_left₀ (by positivity) (hB x hx) r

def sampleBadIndices {N r : Nat} [NeZero N] {I : Type*}
    (Q : Finset I) (Z : I → Finset (ZMod N)) (e : Fin r → ZMod N) : Finset I :=
  Q.filter fun q => ∃ c ∈ nonzeroTernaryCoefficients N r, linearSampleValue c e ∈ Z q

theorem sample_bad_indices_sum_le {N r : Nat} [NeZero N] [Fact N.Prime]
    (hr : 0 < r) {I : Type*} (Q : Finset I) (Z : I → Finset (ZMod N)) {eta : Real}
    (hZ : ∀ q ∈ Q, ((Z q).card : Real) ≤ eta*N) :
    ∑ e : Fin r → ZMod N, ((sampleBadIndices Q Z e).card : Real) ≤
      (3 : Real)^r*eta*(N : Real)^r*Q.card := by
  have hsum : ∑ e : Fin r → ZMod N, (sampleBadIndices Q Z e).card =
      ∑ q ∈ Q, (ternarySamplesMeeting (r := r) (Z q)).card := by
    simp only [sampleBadIndices, ternarySamplesMeeting, Finset.card_filter]
    exact Finset.sum_comm
  have hsumR : ∑ e : Fin r → ZMod N, ((sampleBadIndices Q Z e).card : Real) =
      ∑ q ∈ Q, ((ternarySamplesMeeting (r := r) (Z q)).card : Real) := by exact_mod_cast hsum
  have hpow : (N : Real)^(r-1)*(N : Real) = (N : Real)^r := by
    rw [←pow_succ]
    congr 1
    omega
  rw [hsumR]
  calc
    ∑ q ∈ Q, ((ternarySamplesMeeting (r := r) (Z q)).card : Real)
      ≤ ∑ q ∈ Q, (3 : Real)^r*((Z q).card : Real)*(N : Real)^(r-1) :=
        Finset.sum_le_sum fun q _ => by exact_mod_cast ternary_samples_meeting_card_le (r := r) (Z q)
    _ ≤ ∑ _q ∈ Q, (3 : Real)^r*(eta*N)*(N : Real)^(r-1) :=
      Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hZ q hq) (by positivity)) (by positivity)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ←hpow]; ring

end LeanProofs.GowersSzemeredi
