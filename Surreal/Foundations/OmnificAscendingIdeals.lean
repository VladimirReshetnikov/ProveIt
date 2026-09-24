import Surreal.Foundations.OmnificPurelyInfiniteIdeal
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# A strictly ascending chain of principal omnific ideals

The ascending-chain and non-Noetherian assertions of `odg:prop:notnormal`.
The generators have exponents 1, 1/2, 1/4, and so on in the actual surreal
field. Every generator is the square of the next.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The monomial with dyadic growth exponent 1/2^n. -/
def omnificDyadicMonomial (n : ℕ) : OmnificInteger.{u} :=
  omnificMonomial ((1 / 2 : SignSequence.{u}) ^ n) (pow_pos (by norm_num) n)

/-- The dyadic principal ideal at stage n. -/
def omnificDyadicIdeal (n : ℕ) : Ideal OmnificInteger.{u} :=
  Ideal.span {omnificDyadicMonomial n}

/-- Each dyadic monomial is the square of its successor. -/
theorem omnificDyadicMonomial_square (n : ℕ) :
    omnificDyadicMonomial.{u} n = omnificDyadicMonomial (n + 1) ^ 2 := by
  apply omnificToSurreal_injective
  simp only [omnificDyadicMonomial, pow_two, map_mul, omnificToSurreal_monomial,
    ← omegaPower_add]
  congr 1
  rw [pow_succ]
  ring

/-- Every consecutive inclusion in the dyadic principal-ideal chain is strict. -/
theorem omnificDyadicIdeal_lt_succ (n : ℕ) :
    omnificDyadicIdeal.{u} n < omnificDyadicIdeal (n + 1) := by
  apply lt_iff_le_not_ge.mpr
  constructor
  · apply Ideal.span_singleton_le_span_singleton.mpr
    exact ⟨omnificDyadicMonomial (n + 1), by
      simpa only [pow_two] using omnificDyadicMonomial_square n⟩
  · intro h
    have hd := Ideal.span_singleton_le_span_singleton.mp h
    have he := omnificMonomial_le_of_dvd _ _ hd
    have hl : (1 / 2 : SignSequence.{u}) ^ (n + 1) < (1 / 2 : SignSequence.{u}) ^ n := by
      rw [pow_succ]
      exact mul_lt_of_lt_one_right (pow_pos (by norm_num) _) (by norm_num)
    exact hl.not_ge he

/-- The whole dyadic ideal sequence is strictly increasing. -/
theorem omnificDyadicIdeal_strictMono : StrictMono (omnificDyadicIdeal.{u}) :=
  strictMono_nat_of_lt_succ omnificDyadicIdeal_lt_succ

/-- The chain never stabilizes at any finite stage. -/
theorem omnificDyadicIdeal_not_eventually_constant :
    ¬ ∃ N, ∀ n, N ≤ n → omnificDyadicIdeal.{u} n = omnificDyadicIdeal N := by
  rintro ⟨N, hN⟩
  exact (omnificDyadicIdeal_lt_succ N).ne (hN (N + 1) (Nat.le_succ N)).symm

/-- The ascending chain condition fails on the native subtype of principal ideals. -/
theorem omnific_principalIdeals_not_wellFounded_gt :
    ¬ WellFounded ((· > ·) : {I : Ideal OmnificInteger.{u} // I.IsPrincipal} →
      {I : Ideal OmnificInteger.{u} // I.IsPrincipal} → Prop) := by
  let f : ℕ → {I : Ideal OmnificInteger.{u} // I.IsPrincipal} := fun n =>
    ⟨omnificDyadicIdeal n, ⟨omnificDyadicMonomial n, rfl⟩⟩
  exact (RelEmbedding.natGT f (fun n => omnificDyadicIdeal_lt_succ n)).not_wellFounded

/-- The omnific ring is not Noetherian: its purely infinite ideal is not finitely generated. -/
theorem omnific_not_isNoetherianRing : ¬ IsNoetherianRing OmnificInteger.{u} := by
  intro h
  letI := h
  exact omnificPurelyInfiniteIdeal_not_fg (IsNoetherian.noetherian _)

/-- In particular, the omnific ring is not a principal ideal domain. -/
theorem omnific_not_isPrincipalIdealRing : ¬ IsPrincipalIdealRing OmnificInteger.{u} := by
  intro h
  letI := h
  exact omnific_not_isNoetherianRing inferInstance

end
end Surreal.Foundations.SignSequence
