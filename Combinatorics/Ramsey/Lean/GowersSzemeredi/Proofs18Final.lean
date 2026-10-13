import GowersSzemeredi.Proofs18FinalEnvelopes
import GowersSzemeredi.Proofs18CoverHeadlineFrom

/-! **The final route** (Notes L.16-final).

All the final bounds from one structure of inputs, `FinalInputs`: recurrence
profiles with polynomial family constants, and a progression phase partition
(the corpus supplies both; see `Proofs18CoverFejerAllDegrees`). Over the class
table `tDegT3`:
* Theorem 18.1 with `d + 4` in every degree, `d + 3` for `d ≥ 8`, and
  `d + 2` for `d ≥ 11` (degrees `0, …, 3` from the corpus exponents and the
  polynomial base envelope);
* Theorem 18.2 with `L + 3` in every length, `L + 2` for `L ≥ 8`, `L + 1` for
  `L ≥ 11`, and `L + 0` for `L ≥ 13` (lengths `L ≤ 5` from the corpus's
  explicit thresholds). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

namespace FinalInputs

variable (I : FinalInputs)
include I

/-- **Theorem 18.1 at `d + c` from `d = k0 + 2`**, once the envelope fits `2^(c+2)·2^k` in
the dimensions `k0, …, 14` (beyond, the closed form gives `16·2^k`). -/
theorem theorem_18_1_of_fit {c d : Nat} (k0 : Nat) (hd : k0 + 2 ≤ d) (hk0 : 2 ≤ k0) (hc : 2 ≤ c)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → polyGenMuJT3 j + 1 ≤ 2 ^ (c + 2) * 2 ^ j) :
    Theorem181AtSharp c d := by
  have henv := I.polyEnvBound (d - 2) (by omega)
  rw [show d - 2 + 2 = d by omega] at henv
  refine theorem181AtSharp_of_polyEnvBound henv ?_
  rw [show d + c = (c + 2) + (d - 2) by omega, pow_add]
  have hC : 16 ≤ 2 ^ (c + 2) :=
    le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact polyGenMuJT3_fit hC hsmall (by omega)

/-- **Theorem 18.2 at `L + c` from `L = k0 + 4`**, once the envelope fits `2^(c+4)·2^k` in
the dimensions `k0, …, 14`. -/
theorem theorem_18_2_of_fit {c L : Nat} (k0 : Nat) (hL : k0 + 4 ≤ L) (hk0 : 2 ≤ k0)
    (hsmall : ∀ j, k0 ≤ j → j ≤ 14 → genMuXK3 j + 2 * j + 22 ≤ 2 ^ (c + 4) * 2 ^ j) :
    Theorem182AtSharp c L := by
  have henv := I.envBound (L - 4) (by omega)
  rw [show L - 4 + 2 = L - 2 by omega] at henv
  have hge := genMuXK3_ge (k := L - 4) (by omega)
  have hLμ : 4 * L + 20 ≤ 2 ^ genMuXK3 (L - 4) := by
    have := Nat.lt_two_pow_self (n := genMuXK3 (L - 4))
    omega
  have hC : 16 ≤ 2 ^ (c + 4) :=
    le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfit := genMuXK3_fit hC hsmall (by omega : k0 ≤ L - 4)
  refine theorem182AtSharp_of_envBound (by omega) henv (by omega) hLμ ?_
  rw [show L + c = (c + 4) + (L - 4) by omega, pow_add]
  omega

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2`.** -/
theorem theorem_18_1_d2 {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d :=
  I.theorem_18_1_of_fit 9 hd (by norm_num) le_rfl fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3`.** -/
theorem theorem_18_1_d3 {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d :=
  I.theorem_18_1_of_fit 6 hd (by norm_num) (by norm_num) fun j _ _ => by
    interval_cases j <;> decide +kernel

/-- **Theorem 18.1 at every degree with `d + 4`.** -/
theorem theorem_18_1_d4 (d : Nat) : Theorem181AtSharp 4 d := by
  match d with
  | 0 => exact theorem_18_1_d4_degree_zero
  | 1 => exact theorem_18_1_d4_degree_one
  | 2 => exact theorem_18_1_d4_degree_two
  | 3 =>
    obtain ⟨K, p, hpp, hp, hK, hpB⟩ := I.phase
    exact theorem_18_1_d4_three_of_phase_partition hpp hp hK hpB
  | d + 4 =>
    exact I.theorem_18_1_of_fit 2 (by omega) (by norm_num) (by norm_num) fun j _ _ => by
      interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 0`.** -/
theorem theorem_18_2_L0 {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  I.theorem_18_2_of_fit 9 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 11` with `L + 1`.** -/
theorem theorem_18_2_L1 {L : Nat} (hL : 11 ≤ L) : Theorem182AtSharp 1 L :=
  I.theorem_18_2_of_fit 7 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length `L ≥ 8` with `L + 2`.** -/
theorem theorem_18_2_L2 {L : Nat} (hL : 8 ≤ L) : Theorem182AtSharp 2 L :=
  I.theorem_18_2_of_fit 4 hL (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

/-- **Theorem 18.2 at every length with `L + 3`.** -/
theorem theorem_18_2_L3 (L : Nat) : Theorem182AtSharp 3 L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_L3_le_five (by omega)
  · exact I.theorem_18_2_of_fit 2 h (by norm_num) fun j _ _ => by interval_cases j <;> decide +kernel

end FinalInputs

end LeanProofs.GowersSzemeredi
