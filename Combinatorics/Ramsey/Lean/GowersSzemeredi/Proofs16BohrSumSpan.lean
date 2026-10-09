import GowersSzemeredi.Proofs16MixedBogolyubov
import GowersSzemeredi.Proofs16BohrSpectrum

/-! Bohr-sum containment from the intersection of bounded frequency spans.
The mixed correlation supplies membership in the sum, and the polynomial
large-spectrum bound supplies the defining frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def polynomialSpectrumCutoff (m : Nat) (rho epsilon : Real) : Nat :=
  ⌈max (8 * (m + 1 : Real) / (epsilon * rho))
    (128 * (m + 1 : Real)^2 / epsilon^2)⌉₊

def bohrSumThreshold {N : Nat} [NeZero N] (K L : Finset (ZMod N)) (rho sigma : Real) : Real :=
  ((bohr K (rho / 2)).card : Real) * (bohr L (sigma / 2)).card / (4 * (N : Real)^2)

/-- The mixed coefficient threshold is positive and at most one. -/
theorem bohrSumThreshold_bounds {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) {rho sigma : Real} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma) :
    0 < bohrSumThreshold K L rho sigma ∧ bohrSumThreshold K L rho sigma ≤ 1 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard (T : Finset (ZMod N)) {r : Real} (hr : 0 ≤ r) :
      0 < ((bohr T r).card : Real) ∧ ((bohr T r).card : Real) ≤ N := by
    constructor
    · exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_bohr T hr⟩
    · exact_mod_cast (show (bohr T r).card ≤ N by simpa using Finset.card_le_univ (bohr T r))
  obtain ⟨hA, hAN⟩ := hcard K (show 0 ≤ rho / 2 by positivity)
  obtain ⟨hB, hBN⟩ := hcard L (show 0 ≤ sigma / 2 by positivity)
  unfold bohrSumThreshold
  refine ⟨by positivity, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have hmul := mul_le_mul hAN hBN hB.le hN.le
  nlinarith [sq_nonneg (N : Real)]

/-- The common large spectrum of the half-radius sets controls their sum. -/
theorem bohr_sum_of_common_spectrum {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) {rho sigma : Real} (hrho : 0 ≤ rho) (hsigma : 0 ≤ sigma)
    (d : ZMod N)
    (hd : d ∈ bohr (commonLargeSpectrum (bohr K (rho / 2)) (bohr L (sigma / 2))
      (bohrSumThreshold K L rho sigma)) (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  obtain ⟨a₁, ha₁, a₂, ha₂, b₁, hb₁, b₂, hb₂, hd'⟩ :=
    mixed_bogolyubov (bohr K (rho / 2)) (bohr L (sigma / 2))
      ⟨0, zero_mem_bohr K (show 0 ≤ rho / 2 by positivity)⟩ ⟨0, zero_mem_bohr L (show 0 ≤ sigma / 2 by positivity)⟩ d hd
  refine ⟨a₁ - a₂, ?_, b₁ - b₂, ?_, hd'⟩
  · simpa only [sub_eq_add_neg] using bohr_add_half ha₁ (neg_mem_bohr ha₂)
  · simpa only [sub_eq_add_neg] using bohr_add_half hb₁ (neg_mem_bohr hb₂)

/-- The intersection of the two bounded frequency spans defines a Bohr
neighborhood contained in the sum of the original Bohr sets. -/
theorem bohr_sum_contains_span_intersection {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hNK : 8 * (K.card + 1 : Real) / bohrSumThreshold K L rho sigma ≤ (N : Real))
    (hNL : 8 * (L.card + 1 : Real) / bohrSumThreshold K L rho sigma ≤ (N : Real))
    (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (bohrSumThreshold K L rho sigma)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (bohrSumThreshold K L rho sigma)))
      (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  obtain ⟨htau, htau1⟩ := bohrSumThreshold_bounds K L hrho.le hsigma.le
  apply bohr_sum_of_common_spectrum K L hrho.le hsigma.le d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hlarge := (Finset.mem_filter.mp hr).2
  have hK := large_bohr_fourier_mem_polynomial_boundedSpan K (half_pos hrho)
    (by linarith : rho / 2 < 1 / 2) htau htau1 hNK hlarge.1
  have hL := large_bohr_fourier_mem_polynomial_boundedSpan L (half_pos hsigma)
    (by linarith : sigma / 2 < 1 / 2) htau htau1 hNL hlarge.2
  exact (Finset.mem_filter.mp hd).2 r (Finset.mem_inter.mpr ⟨hK, hL⟩)

end LeanProofs.GowersSzemeredi
