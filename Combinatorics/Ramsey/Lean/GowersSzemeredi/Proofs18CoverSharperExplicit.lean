import GowersSzemeredi.Proofs18CoverExplicit
import GowersSzemeredi.Proofs18CoverSharper
import GowersSzemeredi.Proofs18CoverTightBase
import GowersSzemeredi.Proofs18CoverColorings

/-! **Sharper exponents for Theorems 18.1 and 18.2, from the explicit
profiles** (Notes L.15).

* `theorem_18_1_sharper_four_le`: Theorem 18.1 at every degree `d ≥ 4` with
  exponent `α^(2^(2^(d+8)))` (printed: `d + 10`);
* `theorem_18_2_sharper_six_le`: Theorem 18.2 at every length `L ≥ 6` with
  threshold `2^(2^(δ⁻¹^(2^(2^(L+6)))))` (printed: `L + 9`);
* with the tight base budget (`Proofs18CoverTightBase`):
  `theorem_18_1_d7_four_le` (exponent `α^(2^(2^(d+7)))`, every `d ≥ 4`) and
  `theorem_18_2_L5_eleven_le` (`L + 5`, every `L ≥ 11`);
* Corollary 18.7 at the same thresholds: `corollary_18_7_sharper_six_le`
  and `corollary_18_7_L5_eleven_le`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at every degree `d ≥ 4` with `d + 8` in place of `d + 10`.** -/
theorem theorem_18_1_sharper_four_le {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 8 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_sharper_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4

/-- **Theorem 18.2 at every length `L ≥ 6` with `L + 6` in place of `L + 9`.** -/
theorem theorem_18_2_sharper_six_le {L : Nat} (hL6 : 6 ≤ L) : Theorem182AtSharp 6 L :=
  theorem_18_2_sharper_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL6

/-- **Theorem 18.1 at every degree `d ≥ 4` with `d + 7` in place of `d + 10`.** -/
theorem theorem_18_1_d7_four_le {d : Nat} (hd4 : 4 ≤ d) : Theorem181AtSharp 7 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d7_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 5` in place of `L + 9`.** -/
theorem theorem_18_2_L5_eleven_le {L : Nat} (hL11 : 11 ≤ L) : Theorem182AtSharp 5 L :=
  theorem_18_2_L5_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL11

/-- **Corollary 18.7 at every length `L ≥ 6` with `L + 6` in place of `L + 9`.** -/
theorem corollary_18_7_sharper_six_le {L : Nat} (hL6 : 6 ≤ L) : Corollary187AtSharp 6 L :=
  (theorem_18_2_sharper_six_le hL6).corollary_18_7

/-- **Corollary 18.7 at every length `L ≥ 11` with `L + 5` in place of `L + 9`.** -/
theorem corollary_18_7_L5_eleven_le {L : Nat} (hL11 : 11 ≤ L) : Corollary187AtSharp 5 L :=
  (theorem_18_2_L5_eleven_le hL11).corollary_18_7

end LeanProofs.GowersSzemeredi
