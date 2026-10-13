import GowersSzemeredi.Proofs18Final
import GowersSzemeredi.Proofs18LengthSixExplicit
import GowersSzemeredi.Proofs16ExplicitVarietyDecomposition
import GowersSzemeredi.Proofs18PolyCubicDegreeExplicit
import GowersSzemeredi.Proofs16ExplicitConstantBounds
import GowersSzemeredi.Proofs16AllDimensionsExplicit
import GowersSzemeredi.Proofs18CoverVanDerWaerden

/-! **The final bounds of Sections 16 and 18** (Notes L.16-final).

The corpus supplies the inputs of the final route (`explicitFinalInputs`):
the recurrence profiles of Section 16, family constants at most
`2^(2^(4k+16))` (`explicit_family_constants_poly_le`), and a progression
phase partition. `Proofs18Final` turns them into
* **Theorem 18.1** with `d + 4` in place of `d + 10` in every degree
  (`theorem_18_1_d4`), `d + 3` for `d ≥ 8`, and `d + 2` for `d ≥ 11`;
* **Theorem 18.2** with `L + 3` in place of `L + 9` in every length
  (`theorem_18_2_L3`), `L + 2` for `L ≥ 8`, `L + 1` for `L ≥ 11`, and no
  offset, `L + 0`, for `L ≥ 13`;
* with each, Corollary 18.7, van der Waerden numbers
  `W(k, r) ≤ 2^2^r^2^2^(k+c)`, and Theorem 1.3 with constant `2^(-2^(k+c))`;
* Theorem 16.2 and Corollary 16.11 with polynomial controls at the classes
  `tDegT3`.
The printed statements follow (`theorem_18_1_d4_implies_printed`,
`theorem_18_2_L3_implies_printed`, `corollary_18_7_L3_implies_printed`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **The explicit family constants are at most `2^(2^(4k+16))`**, a double
logarithm linear in `k`. -/
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

/-- **The corpus inputs of the final route.** -/
def explicitFinalInputs : FinalInputs where
  Kc k := ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊
  pc k := (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))
  two_le_Kc k := two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
  pc_pos k := Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _)
  profile k _ := section16RecurrenceProfileWith_explicit k
  const := explicit_family_constants_poly_le
  phase := progressionPhasePartition_explicit

/-! ### Theorem 18.1 -/

/-- **Theorem 18.1 at every degree with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d :=
  explicitFinalInputs.theorem_18_1_d4 d

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3` in place of `d + 10`.** -/
theorem theorem_18_1_d3_eight_le {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d :=
  explicitFinalInputs.theorem_18_1_d3 hd

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_eleven_le {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d :=
  explicitFinalInputs.theorem_18_1_d2 hd

/-- The `d + 4` statement implies the catalogue's Theorem 18.1. -/
theorem theorem_18_1_d4_implies_printed : theorem_18_1 :=
  theorem_18_1_iff_forall_degree.mpr fun d =>
    (theorem181AtSharp_ten_iff d).mp ((theorem_18_1_d4 d).mono (by norm_num))

/-! ### Theorem 18.2, Corollary 18.7, van der Waerden numbers, Theorem 1.3 -/

/-- **Theorem 18.2 at every length with `L + 3` in place of `L + 9`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L :=
  explicitFinalInputs.theorem_18_2_L3 L

/-- **Corollary 18.7 at every length with `L + 3` in place of `L + 9`.** -/
theorem corollary_18_7_L3 (L : Nat) : Corollary187AtSharp 3 L :=
  (theorem_18_2_L3 L).corollary_18_7

/-- The `L + 3` statement implies the catalogue's Theorem 18.2. -/
theorem theorem_18_2_L3_implies_printed : theorem_18_2 :=
  theorem_18_2_iff_forall_length.mpr fun L _ =>
    (theorem182AtSharp_nine_iff L).mp ((theorem_18_2_L3 L).mono (by norm_num))

/-- The `L + 3` statement implies the catalogue's Corollary 18.7. -/
theorem corollary_18_7_L3_implies_printed : corollary_18_7 :=
  corollary_18_7_iff_forall_length.mpr fun L _ =>
    (corollary187AtSharp_nine_iff L).mp (((theorem_18_2_L3 L).mono (by norm_num)).corollary_18_7)

/-- **Van der Waerden numbers**: every `r`-colouring of `[1, N]` with `r ≥ 2`
has a monochromatic `k`-term progression once `N` reaches the threshold with
`k + 3` on top, so `W(k, r) ≤ 2^2^r^2^2^(k+3)` for every `k` (Gowers prints
`k + 9`). -/
theorem van_der_waerden_L3_all (k : Nat) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 3 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L3 k).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+3))`** for every `k` (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L3 : Theorem13At 3 :=
  theorem13At_of_sharp theorem_18_2_L3

/-- **Theorem 18.2 at every length `L ≥ 8` with `L + 2` in place of `L + 9`.** -/
theorem theorem_18_2_L2_eight_le {L : Nat} (hL : 8 ≤ L) : Theorem182AtSharp 2 L :=
  explicitFinalInputs.theorem_18_2_L2 hL

/-- **Corollary 18.7 at every length `L ≥ 8` with `L + 2`.** -/
theorem corollary_18_7_L2_eight_le {L : Nat} (hL : 8 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_eight_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 8` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+2)`. -/
theorem van_der_waerden_L2_eight_le {k : Nat} (hk : 8 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 2 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L2_eight_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with `k + 2` for every `k ≥ 8`.** -/
theorem theorem_1_3_L2_eight_le : Theorem13AtFrom 2 8 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L2_eight_le hk

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 1` in place of `L + 9`.** -/
theorem theorem_18_2_L1_eleven_le {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 1 L :=
  explicitFinalInputs.theorem_18_2_L1 hL

/-- **Corollary 18.7 at every length `L ≥ 11` with `L + 1`.** -/
theorem corollary_18_7_L1_eleven_le {L : Nat} (hL : 11 ≤ L) : Corollary187AtSharp 1 L :=
  (theorem_18_2_L1_eleven_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 11` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+1)`. -/
theorem van_der_waerden_L1_eleven_le {k : Nat} (hk : 11 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 1 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L1_eleven_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with `k + 1` for every `k ≥ 11`.** -/
theorem theorem_1_3_L1_eleven_le : Theorem13AtFrom 1 11 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L1_eleven_le hk

/-- **Theorem 18.2 at every length `L ≥ 13` with no offset.** -/
theorem theorem_18_2_L0_thirteen_le {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  explicitFinalInputs.theorem_18_2_L0 hL

/-- **Corollary 18.7 at every length `L ≥ 13` with no offset.** -/
theorem corollary_18_7_L0_thirteen_le {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_thirteen_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 13` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0_thirteen_le {k : Nat} (hk : 13 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_thirteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 13`.** -/
theorem theorem_1_3_L0_thirteen_le : Theorem13AtFrom 0 13 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_thirteen_le hk

/-! ### Theorem 16.2 and Corollary 16.11 at the classes `tDegT3` -/

/-- **Theorem 16.2 with polynomial controls at the classes `tDegT3`.** -/
theorem theorem_16_2_polynomial_fejerT3 {k : Nat} (hk : 1 ≤ k) :
    PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegT3 k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegT3 k)) :=
  explicitFinalInputs.theorem_16_2_polynomial hk

/-- **Corollary 16.11 with exponent `(2/α)^(-2^(2·tDegT3 k + 7k + 38))`.** -/
theorem corollary_16_11_polynomial_fejerJT3 {k : Nat} (hk : 2 ≤ k) :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 / 2 →
      ∃ e : Real, 0 < e ∧ e⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 * tDegT3 k + 7 * k + 38)) ∧
        ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
          ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (k + 2) →
            ∃ P : Box N (k + 1), ∃ mu : Point N (k + 1) → ZMod N,
              IsMultilinear mu ∧ (N : Real) ^ e ≤ P.width ∧
              e * P.carrier.card ≤ section16LargeMultilinearFrequencyCount f P mu alpha := by
  intro alpha ha ha2
  obtain ⟨e, he0, hei, hN⟩ := explicitFinalInputs.corollary_16_11_polynomial hk alpha ha ha2
  exact ⟨e, he0, pw_mono (two_div_ge_two ha ha2) hei (expDegJT3_tight_le k), hN⟩

end LeanProofs.GowersSzemeredi
