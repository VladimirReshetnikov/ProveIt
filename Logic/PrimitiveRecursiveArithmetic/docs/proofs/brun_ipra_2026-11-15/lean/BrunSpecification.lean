import Mathlib

/-!
# Finite specification for constructive Brun convergence

Status: specification and candidate conditional assembly proofs, uncompiled.
The source contains no `sorry` and no new axioms. No kernel verification is
claimed. It does NOT prove the sieve bound or an object-language iPRA
derivation. See FORMALIZATION_PLAN.md for the remaining work.

Intended integration target: ProveIt commit
8c135f6f2a9d041cde785a1a632c44ad98065b20, Lean/Mathlib v4.32.0.
The module uses only the semantic Mathlib layer. The deeply embedded target
is described separately in the plan.
-/

set_option autoImplicit false

namespace BrunIPRA

open scoped BigOperators

/-- Trial division with an explicitly bounded list. -/
def primeB (n : ℕ) : Bool :=
  decide (2 ≤ n) &&
    (List.range n).all (fun d => decide (d < 2 ∨ n % d ≠ 0))

def twinB (p : ℕ) : Bool := primeB p && primeB (p + 2)

/-- Strict cutoff: each pair is indexed by its smaller member.
The prime 5 therefore occurs in both pairs (3,5) and (5,7). -/
def brunPartial (N : ℕ) : ℚ :=
  ∑ p ∈ Finset.range N,
    if twinB p then (1 : ℚ) / (p : ℚ) + 1 / ((p + 2 : ℕ) : ℚ) else 0

def sieveConstant : ℕ := 2 ^ 11

def exponentIndex (q : ℕ) : ℕ := 2 ^ (q + 13)

def cutoff (q : ℕ) : ℕ := 2 ^ exponentIndex q

def epsilon (q : ℕ) : ℚ := 1 / (2 : ℚ) ^ q

/-- For p < B, both p and p+2 divide (B+1)! when they are positive. -/
def commonDenominator (B : ℕ) : ℕ := (B + 1).factorial

/-- Denominator-cleared finite pair sum over A ≤ p < B.
The zero-denominator cases have coefficient zero because primeB rejects
0 and 1. -/
def tailNumerator (A B : ℕ) : ℕ :=
  ∑ p ∈ Finset.Ico A B,
    if twinB p then
      commonDenominator B / p + commonDenominator B / (p + 2)
    else 0

/-- Closed arithmetic target, with only natural-number computations in
the matrix. Its Boolean characteristic is the formula to encode in PRAAx. -/
def ArithmeticBrunClaim : Prop :=
  ∀ q A B : ℕ, cutoff q ≤ A → A ≤ B →
    2 ^ q * tailNumerator A B ≤ commonDenominator B

/-- The principal finite tail theorem supplied by the human proof.
It is a proposition to be proved, not an axiom or a theorem in this file. -/
def DyadicTailClaim : Prop :=
  ∀ m L : ℕ, 1 ≤ m → 2 ^ m ≤ L →
    0 ≤ brunPartial L - brunPartial (2 ^ m) ∧
    brunPartial L - brunPartial (2 ^ m) ≤
      ((4 * sieveConstant : ℕ) : ℚ) / (m : ℚ)

/-- The semantic Cauchy statement, with the explicit primitive-recursive
cutoff and no quantification over real numbers. -/
def BrunCauchyClaim : Prop :=
  ∀ q M L : ℕ, cutoff q ≤ M → cutoff q ≤ L →
    |brunPartial M - brunPartial L| ≤ epsilon q

/-- Candidate proof that a finite interval enclosure implies a Cauchy estimate.
Uncompiled; this order lemma does not assert the number-theoretic enclosure. -/
theorem cauchy_of_enclosure
    (a : ℕ → ℚ) (cut : ℕ → ℕ) (err : ℕ → ℚ)
    (h : ∀ q n, cut q ≤ n →
      a (cut q) ≤ a n ∧ a n ≤ a (cut q) + err q) :
    ∀ q i j, cut q ≤ i → cut q ≤ j → |a i - a j| ≤ err q := by
  intro q i j hi hj
  rcases h q i hi with ⟨hi₀, hi₁⟩
  rcases h q j hj with ⟨hj₀, hj₁⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem exponentIndex_pos (q : ℕ) : 1 ≤ exponentIndex q := by
  change 0 < exponentIndex q
  unfold exponentIndex
  positivity

theorem constant_identity (q : ℕ) :
    ((4 * sieveConstant : ℕ) : ℚ) / (exponentIndex q : ℚ) = epsilon q := by
  have htwo : (2 : ℚ) ^ q ≠ 0 := pow_ne_zero q (by norm_num)
  simp only [sieveConstant, exponentIndex, epsilon, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  norm_num <;> field_simp [htwo] <;> ring

/-- Candidate conditional assembly proof, uncompiled: a proof of the finite
dyadic tail theorem yields the quantitative Cauchy theorem.
No sieve lemma is hidden here. -/
theorem brunCauchy_of_dyadicTail (h : DyadicTailClaim) : BrunCauchyClaim := by
  unfold BrunCauchyClaim
  apply cauchy_of_enclosure brunPartial cutoff epsilon
  intro q n hn
  have hp := h (exponentIndex q) n (exponentIndex_pos q) hn
  rcases hp with ⟨hlo, hhi⟩
  rw [constant_identity] at hhi
  change 0 ≤ brunPartial n - brunPartial (cutoff q) at hlo
  change brunPartial n - brunPartial (cutoff q) ≤ epsilon q at hhi
  constructor <;> linarith

end BrunIPRA

