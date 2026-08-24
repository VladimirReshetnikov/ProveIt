import GowersSzemeredi.Sections01_03

/-!
# Gowers (2001), Section 4: conjectural statements

Section 4 contains no theorem or lemma, but it does contain two explicitly
numbered conjectures.  They are included for completeness as non-asserting
`Prop`-valued definitions.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Number of ordered (possibly constant) modular progressions of a prescribed
length contained in `A`. -/
def modularProgressionCount {N : Nat} [NeZero N] (length : Nat)
    (A : Finset (ZMod N)) : Nat :=
  countWhere fun p : ZMod N × ZMod N =>
    ∀ i : Fin length, p.1 + (i : Nat) * p.2 ∈ A

/-- A real error function tends to zero through positive arguments. -/
def TendsToZeroAtZero (beta : Real → Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon → ∃ alpha0 : Real, 0 < alpha0 ∧
    ∀ alpha : Real, 0 < alpha → alpha < alpha0 → |beta alpha| < epsilon

/-- **Conjecture 4.1.** -/
def conjecture_4_1 : Prop :=
  ∀ delta : Real, 0 < delta → delta ≤ 1 →
    ∃ beta : Real → Real, TendsToZeroAtZero beta ∧
      ∀ (N : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha : Real),
        (A.card : Real) = delta * N → UniformSetOfDegree A alpha 1 →
        (delta ^ 4 - beta alpha) * (N : Real) ^ 2 ≤
          modularProgressionCount 4 A

/-- **Conjecture 4.2.** -/
def conjecture_4_2 : Prop :=
  ∀ (k : Nat), Even k → ∀ delta : Real, 0 < delta → delta ≤ 1 →
    ∃ beta : Real → Real, TendsToZeroAtZero beta ∧
      ∀ (N : Nat) [NeZero N] (A : Finset (ZMod N)) (alpha : Real),
        (A.card : Real) = delta * N → UniformSetOfDegree A alpha (k - 1) →
        (delta ^ (k + 2) - beta alpha) * (N : Real) ^ 2 ≤
          modularProgressionCount (k + 2) A

end LeanProofs.GowersSzemeredi
