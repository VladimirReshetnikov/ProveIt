import GowersSzemeredi.Proofs18PolyCubicDegreeExplicit
import GowersSzemeredi.Proofs18GenericLengthsExplicit
import GowersSzemeredi.Proofs18CoverDegrees
import GowersSzemeredi.Proofs18Consequences
import GowersSzemeredi.Proofs01QuantitativeHeadline

/-! **Theorem 18.1, Theorem 18.2 and Corollary 18.7, in full** (Notes L.12).

The explicit recurrence profiles (`section16RecurrenceProfileWith_explicit`)
and the explicit phase partition (`progressionPhasePartition_explicit`) feed
the joint-cover envelopes of `Proofs18CoverDegrees`:
* `theorem_18_1_four_le`: Theorem 18.1 at every degree `d ≥ 4`; with the
  degrees below four already proved, `theorem_18_1_explicit : theorem_18_1`;
* `theorem_18_2_six_le`: Theorem 18.2 at every length `L ≥ 6`; with
  `theorem_18_2_le_five`, `theorem_18_2_explicit : theorem_18_2`;
* `corollary_18_7_explicit : corollary_18_7`;
* `theorem_1_2_explicit` and `theorem_1_3_explicit`, through the corpus's
  reductions of Theorems 1.2 and 1.3 to Theorem 18.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.1 at every degree `d ≥ 4`**, with the joint-cover remainder. -/
theorem theorem_18_1_four_le {d : Nat} (hd4 : 4 ≤ d) : Theorem181At d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hpp hp hK hpB hd4

/-- **Theorem 18.1 at every degree.** -/
theorem theorem_18_1_at (d : Nat) : Theorem181At d := by
  rcases Nat.lt_or_ge d 4 with h | h
  · exact theorem_18_1_le_seven (by omega)
  · exact theorem_18_1_four_le h

/-- **Theorem 18.1.** -/
theorem theorem_18_1_explicit : theorem_18_1 :=
  theorem_18_1_iff_forall_degree.mpr theorem_18_1_at

/-- **Theorem 18.2 at every length `L ≥ 6`**, with the joint-cover remainder. -/
theorem theorem_18_2_six_le {L : Nat} (hL6 : 6 ≤ L) : Theorem182At L :=
  theorem_18_2_of_profiles_cover
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_le k) hL6

/-- **Theorem 18.2 at every length.** -/
theorem theorem_18_2_at (L : Nat) : Theorem182At L := by
  rcases Nat.lt_or_ge L 6 with h | h
  · exact theorem_18_2_le_five (by omega)
  · exact theorem_18_2_six_le h

/-- **Theorem 18.2.** -/
theorem theorem_18_2_explicit : theorem_18_2 :=
  theorem_18_2_iff_forall_length.mpr fun L _ => theorem_18_2_at L

/-- **Corollary 18.7.** -/
theorem corollary_18_7_explicit : corollary_18_7 :=
  corollary_18_7_iff_forall_length.mpr fun L _ => (theorem_18_2_at L).corollary_18_7

/-- **Theorem 1.2**, through Theorem 18.2. -/
theorem theorem_1_2_explicit : theorem_1_2 :=
  theorem_1_2_holds_of_theorem_18_2 theorem_18_2_explicit

/-- **Theorem 1.3**, through Theorem 18.2. -/
theorem theorem_1_3_explicit : theorem_1_3 :=
  theorem_1_3_holds_of_theorem_18_2 theorem_18_2_explicit

end LeanProofs.GowersSzemeredi
