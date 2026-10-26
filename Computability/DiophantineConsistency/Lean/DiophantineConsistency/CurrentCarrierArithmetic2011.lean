import DiophantineConsistency.CurrentMasks2011
import DiophantineConsistency.ThirteenCarrierComplete

/-!
# Arithmetic equivalence at the complete maintained length2011 masks

The two masks are exactly `CurrentMasks2011.lowPort` and `highPort`;
the fourth scalar port is the high mask plus beta. Only the kernel
coefficient K remains a parameter. Its positivity suffices for the
existence equivalence of the actual fourteen-variable polynomial and
all three thirteen-variable polynomials. No machine, tableau, or
consistency hypothesis occurs in these arithmetic equivalences.
-/

namespace DiophantineConsistency.CurrentCarrierArithmetic2011

open CurrentMasks2011

/-- A small lower bound without expanding the complete radix integer. -/
theorem beta_ge_thirty_one : 31 ≤ beta := by
  have hr : 32 ≤ radix := by decide
  have hp : radix ≤ radix ^ 2011 :=
    le_self_pow₀ (by decide : 1 ≤ radix) (by decide : 2011 ≠ 0)
  unfold beta
  omega

/-- Every bound needed by Carrier65 follows from the exact finite masks. -/
theorem portBounds (K : ℤ) (hK : 0 < K) : Carrier65Witness.PortBounds (ports K) := by
  refine ⟨?_, hK, ?_, ?_, ?_, ?_⟩
  · change 31 ≤ (beta : ℤ)
    exact_mod_cast beta_ge_thirty_one
  · change 0 < (lowPort : ℤ)
    exact_mod_cast lowPort_pos
  · change (lowPort : ℤ) < (beta : ℤ)
    exact_mod_cast lowPort_lt
  · change (beta : ℤ) < ((highPort + beta : ℕ) : ℤ)
    exact_mod_cast (Nat.lt_add_of_pos_left highPort_pos : beta < highPort + beta)
  · change ((highPort + beta : ℕ) : ℤ) < 2 * (beta : ℤ)
    have h : highPort + beta < 2 * beta := by have := highPort_lt; omega
    exact_mod_cast h

noncomputable def polynomial65 (K : ℤ) : MvPolynomial (Fin 14) ℤ :=
  Carrier65.polynomial (ports K)

noncomputable def polynomial69 (K : ℤ) : MvPolynomial (Fin 13) ℤ :=
  ThirteenCarrier.polynomial69 (ports K)

noncomputable def polynomial70 (K : ℤ) : MvPolynomial (Fin 13) ℤ :=
  ThirteenCarrier.polynomial70 (ports K)

noncomputable def polynomial71 (K : ℤ) : MvPolynomial (Fin 13) ℤ :=
  ThirteenCarrier.polynomial71 (ports K)

/-- Existence always means strictly positive integral independent coordinates. -/
def PositiveZero {n : ℕ} (P : MvPolynomial (Fin n) ℤ) : Prop :=
  ∃ v : Fin n → ℤ, (∀ j, 0 < v j) ∧ MvPolynomial.eval v P = 0

/-- The complete current masks discharge both the native arithmetic interface
and the extra rank-selecting residue. The private Pell seed is constructed. -/
theorem completes (K : ℤ) (hK : 0 < K) (v : Fin 14 → ℤ)
    (hv : ∀ j, 0 < v j) (hz : MvPolynomial.eval v (polynomial65 K) = 0) :
    ∃ u : Fin 13 → ℤ, (∀ j, 0 < u j) ∧ ThirteenCarrierComplete.SameOuter v u ∧
      MvPolynomial.eval u (polynomial69 K) = 0 ∧
      MvPolynomial.eval u (polynomial70 K) = 0 ∧
      MvPolynomial.eval u (polynomial71 K) = 0 := by
  exact ThirteenCarrierComplete.polynomial_zero_completes (ports K) (portBounds K hK)
    (interface K hK.le) lowPort_four v hv hz

/-- The explicit restored assignment handles a zero of any of the three
thirteen-variable forms with the same entire four-port tuple. -/
theorem restores (K : ℤ) (u : Fin 13 → ℤ) (hu : ∀ j, 0 < u j)
    (hz : MvPolynomial.eval u (polynomial69 K) = 0 ∨
      MvPolynomial.eval u (polynomial70 K) = 0 ∨
      MvPolynomial.eval u (polynomial71 K) = 0) :
    (∀ j, 0 < ThirteenCarrierSoundness.restored (ports K) u j) ∧
      MvPolynomial.eval (ThirteenCarrierSoundness.restored (ports K) u)
        (polynomial65 K) = 0 := by
  have hb : 0 < ports K 0 := by
    change 0 < (beta : ℤ)
    exact_mod_cast beta_pos
  exact ThirteenCarrierSoundness.polynomial_zero_restores (ports K) u hb hu hz

theorem positive_zero_65_iff_69 (K : ℤ) (hK : 0 < K) :
    PositiveZero (polynomial65 K) ↔ PositiveZero (polynomial69 K) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨u, hu, _, h69, _, _⟩ := completes K hK v hv hz
    exact ⟨u, hu, h69⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨ThirteenCarrierSoundness.restored (ports K) u,
      restores K u hu (Or.inl hz)⟩

/-- These adjacent thirteen-variable equivalences preserve the entire
assignment; they need no positivity premise on K. -/
theorem positive_zero_69_iff_70 (K : ℤ) :
    PositiveZero (polynomial69 K) ↔ PositiveZero (polynomial70 K) := by
  have hb : 0 < ports K 0 := by
    change 0 < (beta : ℤ)
    exact_mod_cast beta_pos
  constructor
  · rintro ⟨u, hu, hz⟩
    have he := ThirteenCarrier.positive_polynomial_zero_sets (ports K) u hb hu
    exact ⟨u, hu, he.2.mpr (he.1.mp hz)⟩
  · rintro ⟨u, hu, hz⟩
    have he := ThirteenCarrier.positive_polynomial_zero_sets (ports K) u hb hu
    exact ⟨u, hu, he.1.mpr (he.2.mp hz)⟩

theorem positive_zero_70_iff_71 (K : ℤ) :
    PositiveZero (polynomial70 K) ↔ PositiveZero (polynomial71 K) := by
  have hb : 0 < ports K 0 := by
    change 0 < (beta : ℤ)
    exact_mod_cast beta_pos
  constructor
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu,
      (ThirteenCarrier.positive_polynomial_zero_sets (ports K) u hb hu).2.mp hz⟩
  · rintro ⟨u, hu, hz⟩
    exact ⟨u, hu,
      (ThirteenCarrier.positive_polynomial_zero_sets (ports K) u hb hu).2.mpr hz⟩

/-- One chain of equivalences for all four literal polynomials, with the
entire masks fixed and only K positive. This does not bind K to a tableau. -/
theorem positive_zero_existence_chain (K : ℤ) (hK : 0 < K) :
    (PositiveZero (polynomial65 K) ↔ PositiveZero (polynomial69 K)) ∧
    (PositiveZero (polynomial69 K) ↔ PositiveZero (polynomial70 K)) ∧
    (PositiveZero (polynomial70 K) ↔ PositiveZero (polynomial71 K)) :=
  ⟨positive_zero_65_iff_69 K hK, positive_zero_69_iff_70 K, positive_zero_70_iff_71 K⟩

theorem positive_zero_65_iff_71 (K : ℤ) (hK : 0 < K) :
    PositiveZero (polynomial65 K) ↔ PositiveZero (polynomial71 K) :=
  (positive_zero_65_iff_69 K hK).trans
    ((positive_zero_69_iff_70 K).trans (positive_zero_70_iff_71 K))

end DiophantineConsistency.CurrentCarrierArithmetic2011
