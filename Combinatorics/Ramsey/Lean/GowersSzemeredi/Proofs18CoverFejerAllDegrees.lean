import GowersSzemeredi.Proofs18CoverSharperAllDegrees
import GowersSzemeredi.Proofs18CoverFejerHeadline
import GowersSzemeredi.Proofs18CoverFejerLowDegrees
import GowersSzemeredi.Proofs18CoverFejerShortLengths
import GowersSzemeredi.Proofs16PolynomialFejer
import GowersSzemeredi.Proofs18CoverFejerHeadlineQ
import GowersSzemeredi.Proofs18CoverHeadlineFrom
import GowersSzemeredi.Proofs16PolynomialFejerQ
import GowersSzemeredi.Proofs18CoverFejerHeadlineS
import GowersSzemeredi.Proofs16PolynomialFejerS
import GowersSzemeredi.Proofs18CoverFejerHeadlineT
import GowersSzemeredi.Proofs18CoverFejerLowDegrees5
import GowersSzemeredi.Proofs18CoverFejerShortLengths3
import GowersSzemeredi.Proofs18CoverFejerHeadlineU
import GowersSzemeredi.Proofs18CoverFejerHeadlineW
import GowersSzemeredi.Proofs18CoverFejerHeadlineX
import GowersSzemeredi.Proofs16PolynomialFejerX
import GowersSzemeredi.Proofs18CoverFejerHeadlineZ
import GowersSzemeredi.Proofs18CoverFejerHeadlineY

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
`68·2^l`.

For large degrees and lengths it gives:
* the additive-slack classes (Notes L.16i): `d + 5` for `d ≥ 12` and `L + 3`
  for `L ≥ 14`;
* the classes from the dimension-two seed at family exponent `32` (Notes
  L.16j): **`d + 4` for every `d ≥ 13`** (`theorem_18_1_d4_thirteen_le`),
  `d + 5` for `d ≥ 9`, and `L + 3` for every `L ≥ 11`, with van der Waerden
  and Theorem 1.3 at `k + 3` from `k = 11`, and the polynomial Theorem 16.2 /
  Corollary 16.11 at `log₂ uDegS k = 4·2^k + 3(k+4)² + 32`;
* the exact small-dimension classes (Notes L.16k): **`d + 5` in every degree**
  (`theorem_18_1_d5`), `d + 4` for every `d ≥ 11`, and **`L + 3` in every
  length** (`theorem_18_2_L3`, `corollary_18_7_L3`), with
  `W(k, r) ≤ 2^2^r^2^2^(k+3)` and Theorem 1.3 at `2^(-2^(k+3))` for every
  `k`;
* the polynomial Bohr radius (Notes L.16l): **`L + 2` for every `L ≥ 13`**
  (`theorem_18_2_L2_thirteen_le`), with van der Waerden and Theorem 1.3 at
  `k + 2` from `k = 13`;
* the polynomial base budget (Notes L.16m): **`d + 3` for every `d ≥ 11`**
  (`theorem_18_1_d3_eleven_le`), `d + 4` for `d ≥ 8`, **`L + 1` for every
  `L ≥ 13`** (`theorem_18_2_L1_thirteen_le`), `L + 2` for `L ≥ 10`, with van
  der Waerden and Theorem 1.3 at `k + 1` from `k = 13` and at `k + 2` from
  `k = 10`;
* class constant `5/2` beyond dimension `12` and the polynomial Lemma 15.6
  threshold (Notes L.16n): **`d + 2` for every `d ≥ 17`**
  (`theorem_18_1_d2_seventeen_le`) and **no offset at all, `L + 0`, for every
  `L ≥ 19`** (`theorem_18_2_L0_nineteen_le`), with `W(k, r) ≤ 2^2^r^2^2^k` and
  Theorem 1.3 at `2^(-2^k)` from `k = 19`. -/
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

/-- **Theorem 16.2 with polynomial controls with additive slack**, in every
dimension `k ≥ 1`: graph count `max(1, (4V/(γθρ))^uDegQ k)`, `log₂ uDegQ k = 14·2^k + 3(k+4)² + 2` with
`V = 2^(2^(2^(k+4)+1))`, and width exponent its inverse (the printed route
gives `2^(68·2^k)`). -/
theorem theorem_16_2_polynomial_fejerQ {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDegQ k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDegQ k)) :=
  theorem_16_2_polynomial_fejerQ_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk

/-- **Corollary 16.11 with polynomial exponents with additive slack**, in
every dimension `k + 1 ≥ 3`: `e⁻¹ ≤ (2/α)^(2^(58·2^k + 9(k+4)² + k + 30))` (the printed
route gives `236·2^k + k + 24`; the printed statement `e⁻¹ = exp(poly(1/α))`). -/
theorem corollary_16_11_polynomial_fejerQ {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (58 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 30)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerQ_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegQ_tight_le (by omega)), hN⟩

/-! ### The small dimension-two seed: `d + 4`, and `d + 5` / `L + 3` from lower thresholds (Notes L.16j) -/

/-- **Theorem 18.1 at every degree `d ≥ 13` with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4_thirteen_le {d : Nat} (hd : 13 ≤ d) : Theorem181AtSharp 4 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d4_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree `d ≥ 9` with `d + 5` in place of `d + 10`**
(the additive-slack classes need `d ≥ 12`). -/
theorem theorem_18_1_d5_nine_le {d : Nat} (hd : 9 ≤ d) : Theorem181AtSharp 5 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d5S_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 3` in place of `L + 9`**
(the additive-slack classes need `L ≥ 14`). -/
theorem theorem_18_2_L3_eleven_le {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 3 L :=
  theorem_18_2_L3S_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 11` with `L + 3`.** -/
theorem corollary_18_7_L3_eleven_le {L : Nat} (hL : 11 ≤ L) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3_eleven_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 11` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+3)`. -/
theorem van_der_waerden_L3_eleven_le {k : Nat} (hk : 11 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 3 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L3_eleven_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+3))` for every `k ≥ 11`** (printed:
`2^(-2^(k+9))`; every `k`: `2^(-2^(k+4))`, `theorem_1_3_L4`). -/
theorem theorem_1_3_L3_eleven_le : Theorem13AtFrom 3 11 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L3_eleven_le hk

/-- **Theorem 16.2 with polynomial controls at the small-seed classes**, in
every dimension `k ≥ 1`: graph count `max(1, (4V/(γθρ))^uDegS k)`,
`log₂ uDegS k = 4·2^k + 3(k+4)² + 32` with `V = 2^(2^(2^(k+4)+1))`, and
width exponent its inverse (the printed route gives `2^(68·2^k)`). -/
theorem theorem_16_2_polynomial_fejerS {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDegS k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDegS k)) :=
  theorem_16_2_polynomial_fejerS_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk

/-- **Corollary 16.11 with polynomial exponents at the small-seed classes**,
in every dimension `k + 1 ≥ 3`: `e⁻¹ ≤ (2/α)^(2^(32·2^k + 9(k+4)² + k + 120))`
(additive slack: `58·2^k`; printed route `236·2^k + k + 24`). -/
theorem corollary_16_11_polynomial_fejerS {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (32 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 120)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerS_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegS_tight_le (by omega)), hN⟩

/-! ### The exact small-dimension classes: `d + 5` and `L + 3` everywhere (Notes L.16k) -/

/-- **Theorem 18.1 at every degree `d ≥ 4` with `d + 5` in place of `d + 10`.** -/
theorem theorem_18_1_d5_four_le {d : Nat} (hd : 4 ≤ d) : Theorem181AtSharp 5 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d5_four_le_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree with `d + 5` in place of `d + 10`.** -/
theorem theorem_18_1_d5 (d : Nat) : Theorem181AtSharp 5 d := by
  match d with
  | 0 => exact theorem_18_1_d5_degree_zero
  | 1 => exact theorem_18_1_d5_degree_one
  | 2 => exact theorem_18_1_d5_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
    exact theorem_18_1_d5_three_of_phase_partition hpp hp hK hpB
  | d + 4 => exact theorem_18_1_d5_four_le (by omega)

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4_eleven_le {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 4 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d4_eleven_le_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length with `L + 3` in place of `L + 9`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L3_le_five (by omega)
  · exact theorem_18_2_L3_six_le_of_profiles_cover
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      (fun k => explicit_family_constants_le k) h

/-- **Corollary 18.7 at every length with `L + 3` in place of `L + 9`.** -/
theorem corollary_18_7_L3 (L : Nat) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3 L).corollary_18_7

/-- **Van der Waerden numbers**: every `r`-colouring of `[1, N]` with `r ≥ 2`
has a monochromatic `k`-term progression once `N` reaches the threshold with
`k + 3` on top, so `W(k, r) ≤ 2^2^r^2^2^(k+3)` for every `k`. -/
theorem van_der_waerden_L3_all (k : Nat) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 3 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L3 k).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+3))`** for every `k` (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L3 : Theorem13At 3 :=
  theorem13At_of_sharp theorem_18_2_L3

/-! ### The polynomial Bohr radius: `L + 2` (Notes L.16l) -/

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 2` in place of `L + 9`.** -/
theorem theorem_18_2_L2_thirteen_le {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 2 L :=
  theorem_18_2_L2_thirteen_le_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 13` with `L + 2`.** -/
theorem corollary_18_7_L2_thirteen_le {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_thirteen_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 13` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+2)`. -/
theorem van_der_waerden_L2 {k : Nat} (hk : 13 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 2 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L2_thirteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+2))` for every `k ≥ 13`** (printed:
`2^(-2^(k+9))`; every `k`: `2^(-2^(k+3))`, `theorem_1_3_L3`). -/
theorem theorem_1_3_L2_thirteen_le : Theorem13AtFrom 2 13 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L2_thirteen_le hk

/-! ### The polynomial base budget: `d + 3`, `L + 1` (Notes L.16m) -/

/-- **The explicit family constants are at most `2^(2^(4k+16))`**, a double
logarithm linear in `k` (the tower `2^(2^(2^(k+5)))` of
`explicit_family_constants_le` is the same estimate, weakened). -/
theorem explicit_family_constants_poly_le (k : Nat) :
    ((⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊ : Nat) : Real) +
        (((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)) : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ (4 * k + 16)) := by
  have hU : uniformSchmidtK (k + 1) ≤ 2 ^ (schmidtKExp k + k + 2) := by
    have h := uniformSchmidtK_le_of (k := k + 1) (B := 2 ^ schmidtKExp k) fun j =>
      (schmidtMonomialK_le_gen j).trans
        (pow_le_pow_right₀ (by norm_num) (schmidtKExp_mono (by have := j.isLt; omega)))
    push_cast at h
    exact h.trans (uniform_base_le k (schmidtKExp k)).1
  have hMK := multiaffinePartitionK_le_of hU (uniform_base_le k (schmidtKExp k)).2 (2 ^ (k + 1))
  have hPu : uniformSchmidtP (k + 1) ≤ 1 + (k + 1) * schmidtPBnd k :=
    uniformSchmidtP_le_of fun j =>
      (schmidtMonomialP_le_gen j).trans (schmidtPBnd_mono (by have := j.isLt; omega))
  exact family_constants_poly_le k hMK hPu (multiaffinePartitionP_le_pow (k + 1) (2 ^ (k + 1)))

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 3` in place of `d + 10`.** -/
theorem theorem_18_1_d3_eleven_le {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 3 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d3_eleven_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4_eight_le {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 4 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d4_eight_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 1` in place of `L + 9`.** -/
theorem theorem_18_2_L1_thirteen_le {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 1 L :=
  theorem_18_2_L1_thirteen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 13` with `L + 1`.** -/
theorem corollary_18_7_L1_thirteen_le {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 1 L :=
  (theorem_18_2_L1_thirteen_le hL).corollary_18_7

/-- **Theorem 18.2 at every length `L ≥ 10` with `L + 2` in place of `L + 9`.** -/
theorem theorem_18_2_L2_ten_le {L : Nat} (hL : 10 ≤ L) : Theorem182AtSharp 2 L :=
  theorem_18_2_L2_ten_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 10` with `L + 2`.** -/
theorem corollary_18_7_L2_ten_le {L : Nat} (hL : 10 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_ten_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 13` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+1)`. -/
theorem van_der_waerden_L1 {k : Nat} (hk : 13 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 1 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L1_thirteen_le hk).van_der_waerden hr N hN color

/-- **Van der Waerden numbers**: for `k ≥ 10` and `r ≥ 2`,
`W(k, r) ≤ 2^2^r^2^2^(k+2)`. -/
theorem van_der_waerden_L2_ten_le {k : Nat} (hk : 10 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 2 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L2_ten_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+1))` for every `k ≥ 13`** (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L1_thirteen_le : Theorem13AtFrom 1 13 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L1_thirteen_le hk

/-- **Theorem 1.3 with constant `2^(-2^(k+2))` for every `k ≥ 10`.** -/
theorem theorem_1_3_L2_ten_le : Theorem13AtFrom 2 10 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L2_ten_le hk

/-! ### Class constant `5/2` and the polynomial Lemma 15.6: `d + 2`, `L + 0` (Notes L.16n) -/

/-- **Theorem 18.1 at every degree `d ≥ 17` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_seventeen_le {d : Nat} (hd : 17 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_seventeen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 19` with no offset** (`L + 0` in place
of `L + 9`). -/
theorem theorem_18_2_L0_nineteen_le {L : Nat} (hL : 19 ≤ L) : Theorem182AtSharp 0 L :=
  theorem_18_2_L0_nineteen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 19` with no offset.** -/
theorem corollary_18_7_L0_nineteen_le {L : Nat} (hL : 19 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_nineteen_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 19` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0 {k : Nat} (hk : 19 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_nineteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 19`** (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L0_nineteen_le : Theorem13AtFrom 0 19 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_nineteen_le hk

/-- **Theorem 16.2 with polynomial controls at the classes of constant `5/2`**, in
every dimension `k ≥ 1`: graph count `max(1, (4V/(γθρ))^uDegX k)` with
`V = 2^(2^(4k+13))` and `log₂ uDegX k = tDegX k` (`5·2^(k−1) + O(k²)`; printed
`68·2^k`). -/
theorem theorem_16_2_polynomial_fejerX {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegX k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegX k)) :=
  theorem_16_2_polynomial_fejerX_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hk

/-- **Corollary 16.11 with polynomial exponents at the classes of constant `5/2`**,
in every dimension `k + 1 ≥ 3`: `e⁻¹ ≤ (2/α)^(2^(3·tDegX k + 6k + 38))`, that is
`7.5·2^k + O(k²)` (printed route `236·2^k`). -/
theorem corollary_16_11_polynomial_fejerX {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (3 * tDegX k + 6 * k + 38)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := corollary_16_11_polynomial_fejerX_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegX_tight_le k), hN⟩

/-! ### The exact class table to dimension `14` (Notes L.16o) -/

/-- **Theorem 18.1 at every degree `d ≥ 16` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_sixteen_le {d : Nat} (hd : 16 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_sixteen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 18` with no offset.** -/
theorem theorem_18_2_L0_eighteen_le {L : Nat} (hL : 18 ≤ L) : Theorem182AtSharp 0 L :=
  theorem_18_2_L0_eighteen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hL

/-- **Corollary 18.7 at every length `L ≥ 18` with no offset.** -/
theorem corollary_18_7_L0_eighteen_le {L : Nat} (hL : 18 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_eighteen_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 18` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0_eighteen_le {k : Nat} (hk : 18 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_eighteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 18`.** -/
theorem theorem_1_3_L0_eighteen_le : Theorem13AtFrom 0 18 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_eighteen_le hk

/-! ### The partition constant charged at `2^(k+9)` (Notes L.16p) -/

/-- **Theorem 18.1 at every degree `d ≥ 15` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_fifteen_le {d : Nat} (hd : 15 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_fifteen_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree `d ≥ 10` with `d + 3` in place of `d + 10`.** -/
theorem theorem_18_1_d3_ten_le {d : Nat} (hd : 10 ≤ d) : Theorem181AtSharp 3 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d3_ten_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree `d ≥ 7` with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4_seven_le {d : Nat} (hd : 7 ≤ d) : Theorem181AtSharp 4 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d4_seven_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

end LeanProofs.GowersSzemeredi
