import GowersSzemeredi.Proofs18GenericLengths
import GowersSzemeredi.Proofs18GradedLengths
import GowersSzemeredi.Proofs16ExplicitRecurrenceProfiles

/-! **Theorem 18.2 and Corollary 18.7 at every length up to thirteen.**

This module is a bridge. `theorem_18_2_upto_ten_of_profiles` (light,
kernel-checked locally) needs the recurrence profiles in every dimension at
constants `Kc k + pc k ≤ 2^(2^(2^(k+5)))`. The explicit multilinear partition
gives them at
* `Kc k = ⌈multiaffinePartitionK (k+1) (2^(k+1))⌉`;
* `pc k = (k+1)·multiaffinePartitionP (k+1) (2^(k+1))`,
with the bound `explicit_family_constants_le`, exactly as for
`theorem_16_2_explicit`. Lengths below six are `theorem_18_2_le_five`.

The imports reach the port's Schmidt constants and the explicit profiles, so
this module is checked on the full-verification host. Every step is an
instantiation of a kernel-checked statement.

Lengths eleven to thirteen use the graded vertex providers at the tight
class degree (`theorem_18_2_upto_thirteen_of_profiles`, Notes L.10–L.10b): the
nest cost drops from `Θ(4^k)` to `Θ(3^k)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.2 at lengths six to ten**, from the explicit profiles. -/
theorem theorem_18_2_six_to_ten {L : Nat} (hL6 : 6 ≤ L) (hL10 : L ≤ 10) : Theorem182At L :=
  theorem_18_2_upto_ten_of_profiles
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL6 hL10

/-- **Theorem 18.2 at every length up to ten**, with the source thresholds. -/
theorem theorem_18_2_le_ten {L : Nat} (hL : L ≤ 10) : Theorem182At L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_le_five (by omega)
  · exact theorem_18_2_six_to_ten h hL

/-- **Corollary 18.7 at every length up to ten.** -/
theorem corollary_18_7_le_ten {L : Nat} (hL : L ≤ 10) : Corollary187At L :=
  (theorem_18_2_le_ten hL).corollary_18_7

/-- **Theorem 18.2 at every length up to thirteen**, with graded vertex providers. -/
theorem theorem_18_2_le_thirteen {L : Nat} (hL : L ≤ 13) : Theorem182At L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_le_five (by omega)
  · exact theorem_18_2_upto_thirteen_of_profiles
      (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
      (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
      (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
      (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
      (fun k _ => section16RecurrenceProfileWith_explicit k)
      (fun k => explicit_family_constants_le k) h hL

/-- **Corollary 18.7 at every length up to thirteen.** -/
theorem corollary_18_7_le_thirteen {L : Nat} (hL : L ≤ 13) : Corollary187At L :=
  (theorem_18_2_le_thirteen hL).corollary_18_7

/-- Theorem 18.2 at every length up to twelve. -/
theorem theorem_18_2_le_twelve {L : Nat} (hL : L ≤ 12) : Theorem182At L :=
  theorem_18_2_le_thirteen (by omega)

/-- Corollary 18.7 at every length up to twelve. -/
theorem corollary_18_7_le_twelve {L : Nat} (hL : L ≤ 12) : Corollary187At L :=
  corollary_18_7_le_thirteen (by omega)

end LeanProofs.GowersSzemeredi
