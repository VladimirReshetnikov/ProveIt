import GowersSzemeredi.Proofs18GenericLengths
import GowersSzemeredi.Proofs16AllDimensionsExplicit

/-! **Theorem 18.2 and Corollary 18.7 at every length up to ten.**

This module is a bridge. `theorem_18_2_upto_ten_of_profiles` (light,
kernel-checked locally) needs the recurrence profiles in every dimension at
constants `Kc k + pc k ≤ 2^(2^(2^(k+5)))`. The explicit multilinear partition
gives them at
* `Kc k = ⌈multiaffinePartitionK (k+1) (2^(k+1))⌉`;
* `pc k = (k+1)·multiaffinePartitionP (k+1) (2^(k+1))`,
with the bound `explicit_family_constants_le`, exactly as for
`theorem_16_2_explicit`. Lengths up to six are `theorem_18_2_le_six`.

The imports reach the port's Schmidt constants and the explicit profiles, so
this module is checked on the full-verification host. Every step is an
instantiation of a kernel-checked statement.

Length eleven and beyond are out of reach of the single-piece route: its
`2^k − 1`-fold nest costs `Θ(4^k)` in log-degree per step (Notes L.7a). -/
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
  · exact theorem_18_2_le_six (by omega)
  · exact theorem_18_2_six_to_ten h hL

/-- **Corollary 18.7 at every length up to ten.** -/
theorem corollary_18_7_le_ten {L : Nat} (hL : L ≤ 10) : Corollary187At L :=
  (theorem_18_2_le_ten hL).corollary_18_7

end LeanProofs.GowersSzemeredi
