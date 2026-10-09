import GowersSzemeredi.Proofs16UniformSpectrumSpan
import GowersSzemeredi.Proofs16BohrLowerBound

/-! Bohr-sum cutoffs depending only on ranks and radii, through Dirichlet
cell counts. Neither the modulus nor the actual Bohr cardinalities enter
the coefficient cutoff. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Lower coefficient thresholds permit larger frequency cutoffs. -/
theorem polynomialSpectrumCutoff_antitone (m : Nat) {rho epsilon epsilon' : Real}
    (hrho : 0 < rho) (heps : 0 < epsilon) (h : epsilon ≤ epsilon') :
    polynomialSpectrumCutoff m rho epsilon' ≤ polynomialSpectrumCutoff m rho epsilon := by
  unfold polynomialSpectrumCutoff
  apply Nat.ceil_mono
  apply max_le_max
  · exact div_le_div_of_nonneg_left (by positivity) (mul_pos heps hrho)
      (mul_le_mul_of_nonneg_right h hrho.le)
  · exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos heps)
      (by nlinarith [sq_nonneg (epsilon' - epsilon)])

/-- A lower mixed threshold from the number of Dirichlet cells. -/
def bohrSumRankThreshold (k l M P : Nat) : Real := 1 / (4 * (M : Real)^k * (P : Real)^l)

theorem bohrSumRankThreshold_pos (k l M P : Nat) [NeZero M] [NeZero P] :
    0 < bohrSumRankThreshold k l M P := by
  have hM : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hP : (0 : Real) < P := by exact_mod_cast NeZero.pos P
  unfold bohrSumRankThreshold
  positivity

/-- The Bohr lower bound removes actual set cardinalities from the threshold. -/
theorem bohrSumRankThreshold_le {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (M P : Nat) [NeZero M] [NeZero P]
    {rho sigma : Real} (hM : 2 ≤ rho * M) (hP : 2 ≤ sigma * P) :
    bohrSumRankThreshold K.card L.card M P ≤ bohrSumThreshold K L rho sigma := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMN : (0 : Real) < M := by exact_mod_cast NeZero.pos M
  have hPN : (0 : Real) < P := by exact_mod_cast NeZero.pos P
  have hA : (N : Real) ≤ (M : Real)^K.card * (bohr K (rho / 2)).card := by
    exact_mod_cast bohr_card_lower K M (show 1 ≤ rho / 2 * M by linarith)
  have hB : (N : Real) ≤ (P : Real)^L.card * (bohr L (sigma / 2)).card := by
    exact_mod_cast bohr_card_lower L P (show 1 ≤ sigma / 2 * P by linarith)
  have hprod := mul_le_mul hA hB hN.le (show 0 ≤ (M : Real)^K.card * (bohr K (rho / 2)).card by positivity)
  unfold bohrSumRankThreshold bohrSumThreshold
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [hprod]

/-- The Bohr-sum containment has coefficient cutoffs independent of both
the modulus and the actual half-radius Bohr densities. -/
theorem bohr_sum_contains_rank_controlled_span {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) (M P : Nat) [NeZero M] [NeZero P]
    {rho sigma : Real} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hM : 2 ≤ rho * M) (hP : 2 ≤ sigma * P) (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (bohrSumRankThreshold K.card L.card M P)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (bohrSumRankThreshold K.card L.card M P)))
      (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  have htpos := bohrSumRankThreshold_pos K.card L.card M P
  have ht := bohrSumRankThreshold_le K L M P hM hP
  have hRK := polynomialSpectrumCutoff_antitone K.card (half_pos hrho) htpos ht
  have hRL := polynomialSpectrumCutoff_antitone L.card (half_pos hsigma) htpos ht
  apply bohr_sum_contains_span_intersection_uniform K L hrho hrho1 hsigma hsigma1 d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  obtain ⟨hrK, hrL⟩ := Finset.mem_inter.mp hr
  exact (Finset.mem_filter.mp hd).2 r (Finset.mem_inter.mpr
    ⟨boundedFrequencySpan_mono _ hRK hrK, boundedFrequencySpan_mono _ hRL hrL⟩)

/-- Choose the Dirichlet cell counts directly from the two radii. -/
def bohrSumRadiusThreshold (k l : Nat) (rho sigma : Real) : Real :=
  bohrSumRankThreshold k l ⌈2 / rho⌉₊ ⌈2 / sigma⌉₊

/-- Fully explicit radius-and-rank control of the bounded-span intersection
whose Bohr set is contained in the sum. No finite-size hypothesis remains. -/
theorem bohr_sum_contains_radius_controlled_span {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (bohrSumRadiusThreshold K.card L.card rho sigma)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (bohrSumRadiusThreshold K.card L.card rho sigma)))
      (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  have hM : 0 < ⌈2 / rho⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hP : 0 < ⌈2 / sigma⌉₊ := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero ⌈2 / rho⌉₊ := ⟨hM.ne'⟩
  letI : NeZero ⌈2 / sigma⌉₊ := ⟨hP.ne'⟩
  apply bohr_sum_contains_rank_controlled_span K L ⌈2 / rho⌉₊ ⌈2 / sigma⌉₊
    hrho hrho1 hsigma hsigma1 _ _ d hd
  · have h := (div_le_iff₀ hrho).mp (Nat.le_ceil (2 / rho))
    nlinarith only [h]
  · have h := (div_le_iff₀ hsigma).mp (Nat.le_ceil (2 / sigma))
    nlinarith only [h]

end LeanProofs.GowersSzemeredi
