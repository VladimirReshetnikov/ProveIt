import GowersSzemeredi.Proofs18CoverSharperExplicit
import GowersSzemeredi.Proofs18CoverSharperLowDegrees
import GowersSzemeredi.Proofs18CoverSharperShortLengths
import GowersSzemeredi.Proofs18CoverThresholdsSharp
import GowersSzemeredi.Proofs18CoverVanDerWaerden
import GowersSzemeredi.Proofs18CoverHeadline
import GowersSzemeredi.Proofs16PolynomialStructure
import GowersSzemeredi.Proofs16PolynomialCorollary

/-! **Theorem 18.1 in every degree with exponent `α^(2^(2^(d+7)))`** (Notes L.15c).

Degrees `0, 1, 2` from the corpus proofs with the sharper constant, degree
three from the polynomial base envelope at the explicit phase partition, and
degrees `d ≥ 4` from the tight-base envelope (`theorem_18_1_d7_four_le`).
At `c = 10` the statement is the catalogue's Theorem 18.1
(`theorem181AtSharp_ten_iff`), so this strengthens `theorem_18_1_explicit`
(`theorem_18_1_d7_implies_printed`).

Likewise Theorem 18.2 and Corollary 18.7 with `L + 6` in place of `L + 9`
in every length (`theorem_18_2_L6`, `corollary_18_7_L6`): lengths `L ≤ 5`
from the corpus's explicit thresholds (`Proofs18CoverSharperShortLengths`),
lengths `L ≥ 6` from the joint-cover envelope.

With the phase-refinement threshold at the exponential level
(`Proofs18CoverThresholdsSharp`), even `L + 5` holds in every length
(`theorem_18_2_L5`, `corollary_18_7_L5`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at every degree with `d + 7` in place of `d + 10`.** -/
theorem theorem_18_1_d7 (d : Nat) : Theorem181AtSharp 7 d := by
  match d with
  | 0 => exact theorem_18_1_d7_degree_zero
  | 1 => exact theorem_18_1_d7_degree_one
  | 2 => exact theorem_18_1_d7_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
    exact theorem_18_1_d7_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact theorem_18_1_d7_four_le (by omega)

/-- The sharper statement implies the catalogue's Theorem 18.1. -/
theorem theorem_18_1_d7_implies_printed : theorem_18_1 :=
  theorem_18_1_iff_forall_degree.mpr fun d =>
    (theorem181AtSharp_ten_iff d).mp ((theorem_18_1_d7 d).mono (by norm_num))

/-- **Theorem 18.2 at every length with `L + 6` in place of `L + 9`.** -/
theorem theorem_18_2_L6 (L : Nat) : Theorem182AtSharp 6 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L6_le_five (by omega)
  · exact theorem_18_2_sharper_six_le h

/-- **Corollary 18.7 at every length with `L + 6` in place of `L + 9`.** -/
theorem corollary_18_7_L6 (L : Nat) : Corollary187AtSharp 6 L :=
  (theorem_18_2_L6 L).corollary_18_7

/-- The sharper statement implies the catalogue's Theorem 18.2. -/
theorem theorem_18_2_L6_implies_printed : theorem_18_2 :=
  theorem_18_2_iff_forall_length.mpr fun L _ =>
    (theorem182AtSharp_nine_iff L).mp ((theorem_18_2_L6 L).mono (by norm_num))

/-- The sharper statement implies the catalogue's Corollary 18.7. -/
theorem corollary_18_7_L6_implies_printed : corollary_18_7 :=
  corollary_18_7_iff_forall_length.mpr fun L _ =>
    (corollary187AtSharp_nine_iff L).mp (((theorem_18_2_L6 L).mono (by norm_num)).corollary_18_7)

/-- **Theorem 18.2 at every length with `L + 5` in place of `L + 9`.** -/
theorem theorem_18_2_L5 (L : Nat) : Theorem182AtSharp 5 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L5_le_five (by omega)
  · exact theorem_18_2_L5_all_of_profiles_cover
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      (fun k => explicit_family_constants_le k) h

/-- **Corollary 18.7 at every length with `L + 5` in place of `L + 9`.** -/
theorem corollary_18_7_L5 (L : Nat) : Corollary187AtSharp 5 L :=
  (theorem_18_2_L5 L).corollary_18_7

/-- **Van der Waerden numbers**: every `r`-colouring of `[1, N]` with `r ≥ 2`
has a monochromatic `k`-term progression once
`N ≥ 2^(2^(r^(2^(2^(k+5)))))` (Gowers prints `k + 9`). -/
theorem van_der_waerden_L5 (k : Nat) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 5 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L5 k).van_der_waerden hr N hN color

/-- Gowers's van der Waerden bound `W(k, r) ≤ 2^2^r^2^2^(k+9)`. -/
theorem van_der_waerden_printed (k : Nat) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 9 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  ((theorem_18_2_L5 k).mono (by norm_num)).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+5))`** (printed: `2^(-2^(k+9))`). -/
theorem theorem_1_3_L5 : Theorem13At 5 :=
  theorem13At_of_sharp theorem_18_2_L5

/-- **Theorem 16.2 with polynomial controls in every dimension `k ≥ 1`**: graph
count `max(1, (4V/(γθρ))^(2^(68·2^k)))` with `V = 2^(2^(2^(k+4)+1))`, and width
exponent its inverse. -/
theorem theorem_16_2_polynomial {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg68 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg68 k)) :=
  theorem_16_2_polynomial_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk

/-- The polynomial form implies the catalogue's Theorem 16.2. -/
theorem theorem_16_2_polynomial_implies_printed : theorem_16_2 := fun k =>
  match k with
  | 0 => theorem_16_2_zero
  | k + 1 => theorem162At_of_polynomial (theorem_16_2_polynomial (by omega))

/-- **Corollary 16.11 with polynomial exponents** in every dimension `k + 1 ≥ 3`:
a box of width `N^e` carrying a multilinear frequency on an `e` fraction, with
`e⁻¹ ≤ (2/α)^(2^(236·2^k + k + 24))` (printed: `e⁻¹ = exp(poly(1/α))`). -/
theorem corollary_16_11_polynomial {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (236 * 2 ^ k + k + 24)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegC_tight_le k), hN⟩

end LeanProofs.GowersSzemeredi
