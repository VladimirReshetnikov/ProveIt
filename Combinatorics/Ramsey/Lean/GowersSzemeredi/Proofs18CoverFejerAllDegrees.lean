import GowersSzemeredi.Proofs18CoverSharperAllDegrees
import GowersSzemeredi.Proofs18CoverFejerHeadline
import GowersSzemeredi.Proofs18CoverFejerLowDegrees
import GowersSzemeredi.Proofs18CoverFejerShortLengths
import GowersSzemeredi.Proofs16PolynomialFejer
import GowersSzemeredi.Proofs18CoverFejerHeadlineQ
import GowersSzemeredi.Proofs18CoverHeadlineFrom

/-! **Theorem 18.1 at `d + 6` and Theorem 18.2 / Corollary 18.7 at `L + 4`
in every degree and length** (Notes L.16d).

The bridge from the light Fejér route to the explicit corpus inputs, the
same inputs as the `d + 7` / `L + 5` bridge (`Proofs18CoverSharperAllDegrees`):
* degrees `0, 1, 2` from the corpus proofs with `6` in place of `10`, degree
  three from the polynomial base envelope (`Proofs18CoverFejerLowDegrees`),
  and degrees `d ≥ 4` from the Fejér envelope (`theorem_18_1_d6_four_le`);
* lengths `L ≤ 5` from the corpus's explicit thresholds
  (`Proofs18CoverFejerShortLengths`), lengths `L ≥ 6` from the Fejér
  envelope.
The printed statements follow (`theorem_18_1_d6_implies_printed`,
`theorem_18_2_L4_implies_printed`, `corollary_18_7_L4_implies_printed`), as
do van der Waerden numbers `W(k, r) ≤ 2^2^r^2^2^(k+4)` and Theorem 1.3 with
constant `2^(-2^(k+4))`.

The route is that of Notes L.16: the Fejér selection in Lemma 15.5, the
tight Bohr radius, and the resulting class degree `23·2^l` in place of
`68·2^l`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at every degree `d ≥ 4` with `d + 6` in place of `d + 10`.** -/
theorem theorem_18_1_d6_four_le {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 6 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d6_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4

/-- **Theorem 18.1 at every degree with `d + 6` in place of `d + 10`.** -/
theorem theorem_18_1_d6 (d : Nat) : Theorem181AtSharp 6 d := by
  match d with
  | 0 => exact theorem_18_1_d6_degree_zero
  | 1 => exact theorem_18_1_d6_degree_one
  | 2 => exact theorem_18_1_d6_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
    exact theorem_18_1_d6_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact theorem_18_1_d6_four_le (by omega)

/-- The `d + 6` statement implies the catalogue's Theorem 18.1. -/
theorem theorem_18_1_d6_implies_printed : theorem_18_1 :=
  theorem_18_1_iff_forall_degree.mpr fun d =>
    (theorem181AtSharp_ten_iff d).mp ((theorem_18_1_d6 d).mono (by norm_num))

/-- **Theorem 18.2 at every length with `L + 4` in place of `L + 9`.** -/
theorem theorem_18_2_L4 (L : Nat) : Theorem182AtSharp 4 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L4_le_five (by omega)
  · exact theorem_18_2_L4_all_of_profiles_cover
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      (fun k => explicit_family_constants_le k) h

/-- **Corollary 18.7 at every length with `L + 4` in place of `L + 9`.** -/
theorem corollary_18_7_L4 (L : Nat) : Corollary187AtSharp 4 L :=
  (theorem_18_2_L4 L).corollary_18_7

/-- The `L + 4` statement implies the catalogue's Theorem 18.2. -/
theorem theorem_18_2_L4_implies_printed : theorem_18_2 :=
  theorem_18_2_iff_forall_length.mpr fun L _ =>
    (theorem182AtSharp_nine_iff L).mp ((theorem_18_2_L4 L).mono (by norm_num))

/-- The `L + 4` statement implies the catalogue's Corollary 18.7. -/
theorem corollary_18_7_L4_implies_printed : corollary_18_7 :=
  corollary_18_7_iff_forall_length.mpr fun L _ =>
    (corollary187AtSharp_nine_iff L).mp (((theorem_18_2_L4 L).mono (by norm_num)).corollary_18_7)

/-- **Van der Waerden numbers**: every `r`-colouring of `[1, N]` with `r ≥ 2`
has a monochromatic `k`-term progression once
`N ≥ 2^(2^(r^(2^(2^(k+4)))))` (Gowers prints `k + 9`). -/
theorem van_der_waerden_L4 (k : Nat) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 4 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L4 k).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+4))`** (printed: `2^(-2^(k+9))`). -/
theorem theorem_1_3_L4 : Theorem13At 4 :=
  theorem13At_of_sharp theorem_18_2_L4

/-- **Theorem 16.2 with polynomial controls at the Fejér classes**, in every
dimension `k ≥ 1`: graph count `max(1, (4V/(γθρ))^(2^(23·2^k)))` with
`V = 2^(2^(2^(k+4)+1))`, and width exponent its inverse (the printed route
gives `2^(68·2^k)`). -/
theorem theorem_16_2_polynomial_fejer {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg23 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg23 k)) :=
  theorem_16_2_polynomial_fejer_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk

/-- **Corollary 16.11 with polynomial exponents at the Fejér classes**, in
every dimension `k + 1 ≥ 3`: `e⁻¹ ≤ (2/α)^(2^(101·2^k + k + 24))` (the printed
route gives `236·2^k + k + 24`; the printed statement `e⁻¹ = exp(poly(1/α))`). -/
theorem corollary_16_11_polynomial_fejer {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (101 * 2 ^ k + k + 24)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejer_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegF_tight_le k), hN⟩

/-! ### Large degrees and lengths: `d + 5` and `L + 3` (Notes L.16i) -/

/-- **Theorem 18.1 at every degree `d ≥ 12` with `d + 5` in place of `d + 10`.** -/
theorem theorem_18_1_d5_twelve_le {d : Nat} (hd : 12 ≤ d) : Theorem181AtSharp 5 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d5_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 14` with `L + 3` in place of `L + 9`.** -/
theorem theorem_18_2_L3_fourteen_le {L : Nat} (hL : 14 ≤ L) : Theorem182AtSharp 3 L :=
  theorem_18_2_L3_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 14` with `L + 3`.** -/
theorem corollary_18_7_L3_fourteen_le {L : Nat} (hL : 14 ≤ L) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3_fourteen_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 14` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+3)`. -/
theorem van_der_waerden_L3 {k : Nat} (hk : 14 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 3 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L3_fourteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+3))` for every `k ≥ 14`** (printed:
`2^(-2^(k+9))`; every `k`: `2^(-2^(k+4))`, `theorem_1_3_L4`). -/
theorem theorem_1_3_L3_fourteen_le : Theorem13AtFrom 3 14 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L3_fourteen_le hk

end LeanProofs.GowersSzemeredi
