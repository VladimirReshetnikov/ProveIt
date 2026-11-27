import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Rankin's progression-free set

Rankin's rule constrains the ternary digits of each prime exponent. The condition
excludes all nonconstant triples of positive integers satisfying `a * c = b * b`,
including triples with a nonintegral rational ratio.
-/

namespace GRHArticle.ProgressionFree

/-- The nonnegative integers whose ternary digits all lie in `{0, 1}`. -/
def greedyExponents : Set ℕ :=
  {n | ∀ d ∈ Nat.digits 3 n, d ≤ 1}

theorem mem_greedyExponents_iff (n : ℕ) :
    n ∈ greedyExponents ↔ n % 3 ≤ 1 ∧ n / 3 ∈ greedyExponents := by
  by_cases hn : n = 0
  · subst n
    simp [greedyExponents]
  · simp only [greedyExponents, Set.mem_setOf_eq,
      Nat.digits_eq_cons_digits_div (by decide : 1 < 3) hn, List.forall_mem_cons]

theorem zero_mem_greedyExponents : 0 ∈ greedyExponents := by simp [greedyExponents]

theorem one_mem_greedyExponents : 1 ∈ greedyExponents := by
  rw [mem_greedyExponents_iff]
  exact ⟨by decide, zero_mem_greedyExponents⟩

/-- There are no carries when summing binary ternary digits. Thus the midpoint
relation forces the three low digits to agree, then recurs on the quotients. -/
theorem threeAPFree_greedyExponents : ThreeAPFree greedyExponents := by
  have noAP (n : ℕ) :
      ∀ ⦃a b c : ℕ⦄, a + b + c = n →
        a ∈ greedyExponents → b ∈ greedyExponents → c ∈ greedyExponents →
        a + c = b + b → a = b := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b c hn ha hb hc h
      by_cases hz : n = 0
      · omega
      obtain ⟨ha₀, ha₁⟩ := (mem_greedyExponents_iff a).mp ha
      obtain ⟨hb₀, hb₁⟩ := (mem_greedyExponents_iff b).mp hb
      obtain ⟨hc₀, hc₁⟩ := (mem_greedyExponents_iff c).mp hc
      have hrem : a % 3 + c % 3 = b % 3 + b % 3 := by omega
      have hdigit : a % 3 = b % 3 := by omega
      have hquot : a / 3 + c / 3 = b / 3 + b / 3 := by omega
      have hsmall : a / 3 + b / 3 + c / 3 < n := by omega
      have hab : a / 3 = b / 3 := ih _ hsmall rfl ha₁ hb₁ hc₁ hquot
      omega
  intro a ha b hb c hc h
  exact noAP (a + b + c) rfl ha hb hc h

/-- For positive integers the multiplicative midpoint relation is equivalent to
its additive form in every prime exponent. -/
theorem mul_eq_mul_iff_prime_exponents {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * c = b * b ↔ ∀ q : ℕ, q.Prime →
      a.factorization q + c.factorization q = b.factorization q + b.factorization q := by
  constructor
  · intro h q _
    have hf : a.factorization + c.factorization = b.factorization + b.factorization := by
      rw [← Nat.factorization_mul ha hc, ← Nat.factorization_mul hb hb, h]
    exact congrArg (fun f : ℕ →₀ ℕ => f q) hf
  · intro h
    apply Nat.factorization_inj (mul_ne_zero ha hc) (mul_ne_zero hb hb)
    rw [Nat.factorization_mul ha hc, Nat.factorization_mul hb hb]
    ext q
    by_cases hq : q.Prime
    · exact h q hq
    · simp [hq]

/-- Any independent three-term-progression-free constraints on the prime
exponents give a progression-free set of positive integers. -/
theorem threeGPFree_of_prime_exponent_rules (rules : ℕ → Set ℕ)
    (hrules : ∀ p : ℕ, p.Prime → ThreeAPFree (rules p)) :
    ThreeGPFree {n : ℕ | n ≠ 0 ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ rules p} := by
  intro a ha b hb c hc h
  apply Nat.factorization_inj ha.1 hb.1
  ext p
  by_cases hp : p.Prime
  · exact hrules p hp (ha.2 p hp) (hb.2 p hp) (hc.2 p hp)
      ((mul_eq_mul_iff_prime_exponents ha.1 hb.1 hc.1).mp h p hp)
  · simp [hp]

/-- Rankin's set of positive integers. -/
def rankinSet : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ greedyExponents}

/-- Rankin's set is progression-free for the rational-ratio convention. -/
theorem threeGPFree_rankinSet : ThreeGPFree rankinSet :=
  threeGPFree_of_prime_exponent_rules _ fun _ _ => threeAPFree_greedyExponents

section OneDigitExchange

variable {ι : Type*}

private def keptDigitPoint (v : ZMod 3 × (ι → ZMod 3)) : Prop :=
  (v.1 = 0 ∨ v.1 = 1) ∧ (∀ j, v.2 j = 0 ∨ v.2 j = 1) ∧ ¬∀ j, v.2 j = 1

private def insertedDigitPoint (v : ZMod 3 × (ι → ZMod 3)) : Prop :=
  v.1 = 2 ∧ ((∀ j, v.2 j = 1) ∨ ∃ i, v.2 i = 2 ∧ ∀ j, j ≠ i → v.2 j = 1)

/-- The one-digit exchange cap. Remove the two binary points whose satellite
digits are all one, then add the marker-two points whose satellite digits are
all one with at most one exception equal to two. -/
def exchangedDigitCap (ι : Type*) : Set (ZMod 3 × (ι → ZMod 3)) :=
  {v | keptDigitPoint v ∨ insertedDigitPoint v}

private theorem eq_of_binary_digits_zero_sum :
    ∀ a b c : ZMod 3,
      (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → (c = 0 ∨ c = 1) →
      a + b + c = 0 → a = b ∧ b = c := by
  decide

private theorem eq_of_one_two_digits_zero_sum :
    ∀ a b c : ZMod 3,
      (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) → (c = 1 ∨ c = 2) →
      a + b + c = 0 → a = b ∧ b = c := by
  decide

private theorem old_digit_eq_one_of_add_two :
    ∀ a b : ZMod 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      a + b + 2 = 0 → a = 1 ∨ b = 1 := by
  decide

private theorem no_old_marker_of_add_two_twice :
    ∀ a : ZMod 3, (a = 0 ∨ a = 1) → a + 2 + 2 ≠ 0 := by
  decide

private theorem digit_three_sum : ∀ a : ZMod 3, a + a + a = 0 := by
  decide

private theorem insertedDigitPoint_satellite {v : ZMod 3 × (ι → ZMod 3)}
    (hv : insertedDigitPoint v) (j : ι) : v.2 j = 1 ∨ v.2 j = 2 := by
  rcases hv.2 with h | ⟨i, hi, hrest⟩
  · exact Or.inl (h j)
  · by_cases hji : j = i
    · exact Or.inr (hji ▸ hi)
    · exact Or.inl (hrest j hji)

private theorem no_two_kept_one_inserted {a b c : ZMod 3 × (ι → ZMod 3)}
    (ha : keptDigitPoint a) (hb : keptDigitPoint b) (hc : insertedDigitPoint c)
    (h : a + b + c = 0) : False := by
  have hsat (j : ι) : a.2 j + b.2 j + c.2 j = 0 :=
    congrArg (fun v : ZMod 3 × (ι → ZMod 3) => v.2 j) h
  have bothOne (j : ι) (hj : c.2 j = 1) : a.2 j = 1 ∧ b.2 j = 1 := by
    obtain ⟨hab, hbc⟩ := eq_of_binary_digits_zero_sum _ _ _
      (ha.2.1 j) (hb.2.1 j) (Or.inr hj) (hsat j)
    exact ⟨hab.trans (hbc.trans hj), hbc.trans hj⟩
  rcases hc.2 with hones | ⟨i, hi, hrest⟩
  · exact ha.2.2 fun j => (bothOne j (hones j)).1
  · have hex := old_digit_eq_one_of_add_two _ _ (ha.2.1 i) (hb.2.1 i)
      (by simpa only [hi] using hsat i)
    rcases hex with hai | hbi
    · apply ha.2.2
      intro j
      by_cases hji : j = i
      · exact hji ▸ hai
      · exact (bothOne j (hrest j hji)).1
    · apply hb.2.2
      intro j
      by_cases hji : j = i
      · exact hji ▸ hbi
      · exact (bothOne j (hrest j hji)).2

private theorem no_one_kept_two_inserted {a b c : ZMod 3 × (ι → ZMod 3)}
    (ha : keptDigitPoint a) (hb : insertedDigitPoint b) (hc : insertedDigitPoint c)
    (h : a + b + c = 0) : False :=
  no_old_marker_of_add_two_twice _ ha.1 (by
    simpa only [Prod.fst_add, Prod.fst_zero, hb.1, hc.1] using congrArg Prod.fst h)

/-- The one-digit exchange cap contains no nonconstant three-term progression
in `(ℤ/3ℤ) × (ι → ℤ/3ℤ)`. -/
theorem threeAPFree_exchangedDigitCap (ι : Type*) : ThreeAPFree (exchangedDigitCap ι) := by
  intro a ha b hb c hc habc
  have hb3 : b + b + b = 0 :=
    Prod.ext (digit_three_sum b.1) (funext fun j => digit_three_sum (b.2 j))
  have h : a + b + c = 0 := calc
    a + b + c = a + c + b := by ac_rfl
    _ = b + b + b := by rw [habc]
    _ = 0 := hb3
  have hmark : a.1 + b.1 + c.1 = 0 := congrArg Prod.fst h
  have hsat (j : ι) : a.2 j + b.2 j + c.2 j = 0 :=
    congrArg (fun v : ZMod 3 × (ι → ZMod 3) => v.2 j) h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Prod.ext (eq_of_binary_digits_zero_sum _ _ _ ha.1 hb.1 hc.1 hmark).1
      (funext fun j => (eq_of_binary_digits_zero_sum _ _ _
        (ha.2.1 j) (hb.2.1 j) (hc.2.1 j) (hsat j)).1)
  · exact (no_two_kept_one_inserted ha hb hc h).elim
  · exact (no_two_kept_one_inserted ha hc hb (by
      simpa only [add_assoc, add_left_comm, add_comm] using h)).elim
  · exact (no_one_kept_two_inserted ha hb hc h).elim
  · exact (no_two_kept_one_inserted hb hc ha (by
      simpa only [add_assoc, add_left_comm, add_comm] using h)).elim
  · exact (no_one_kept_two_inserted hb ha hc (by
      simpa only [add_assoc, add_left_comm, add_comm] using h)).elim
  · exact (no_one_kept_two_inserted hc ha hb (by
      simpa only [add_assoc, add_left_comm, add_comm] using h)).elim
  · exact Prod.ext (ha.1.trans hb.1.symm)
      (funext fun j => (eq_of_one_two_digits_zero_sum _ _ _
        (insertedDigitPoint_satellite ha j) (insertedDigitPoint_satellite hb j)
        (insertedDigitPoint_satellite hc j) (hsat j)).1)

private def exponentDigits (marker : ℕ) (satellites : Finset ℕ) (n : ℕ) :
    ZMod 3 × (↥satellites → ZMod 3) :=
  (n.factorization marker, fun q => n.factorization q.val)

/-- The one-digit modification of Rankin's set. The exponent residues at the
marker and satellites lie in the exchanged cap. The higher ternary digits at
those primes, and all ternary digits at other primes, are binary. -/
def exchangedRankinSet (marker : ℕ) (satellites : Finset ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ exponentDigits marker satellites n ∈ exchangedDigitCap ↥satellites ∧
    ∀ p : ℕ, p.Prime →
      if p = marker ∨ p ∈ satellites then n.factorization p / 3 ∈ greedyExponents
      else n.factorization p ∈ greedyExponents}

private theorem mod_eq_of_exponentDigits_eq {marker a b : ℕ} {satellites : Finset ℕ}
    (h : exponentDigits marker satellites a = exponentDigits marker satellites b)
    {p : ℕ} (hp : p = marker ∨ p ∈ satellites) :
    a.factorization p % 3 = b.factorization p % 3 := by
  rcases hp with rfl | hp
  · simpa only [exponentDigits, ZMod.val_natCast] using congrArg (fun v => v.1.val) h
  · simpa only [exponentDigits, ZMod.val_natCast] using
      congrArg (fun v => (v.2 ⟨p, hp⟩).val) h

/-- The one-digit exchange remains progression-free even for rational ratios. -/
theorem threeGPFree_exchangedRankinSet (marker : ℕ) (satellites : Finset ℕ)
    (hmarker : marker.Prime) (hsatellites : ∀ p ∈ satellites, Nat.Prime p) :
    ThreeGPFree (exchangedRankinSet marker satellites) := by
  intro a ha b hb c hc habc
  have hval := (mul_eq_mul_iff_prime_exponents ha.1 hb.1 hc.1).mp habc
  have hcast (p : ℕ) (hp : p.Prime) :
      (a.factorization p : ZMod 3) + (c.factorization p : ZMod 3) =
        (b.factorization p : ZMod 3) + (b.factorization p : ZMod 3) := by
    simpa only [Nat.cast_add] using congrArg (fun k : ℕ => (k : ZMod 3)) (hval p hp)
  have hlow : exponentDigits marker satellites a + exponentDigits marker satellites c =
      exponentDigits marker satellites b + exponentDigits marker satellites b :=
    Prod.ext (hcast marker hmarker) (funext fun p => hcast p.val (hsatellites p.val p.property))
  have hablow := threeAPFree_exchangedDigitCap ↥satellites ha.2.1 hb.2.1 hc.2.1 hlow
  rw [hablow] at hlow
  have hbclow := (add_left_cancel hlow).symm
  apply Nat.factorization_inj ha.1 hb.1
  ext p
  by_cases hp : p.Prime
  · have h := hval p hp
    by_cases hspecial : p = marker ∨ p ∈ satellites
    · have hremAB := mod_eq_of_exponentDigits_eq hablow hspecial
      have hremBC := mod_eq_of_exponentDigits_eq hbclow hspecial
      have hqa : a.factorization p / 3 ∈ greedyExponents := by
        simpa only [if_pos hspecial] using ha.2.2 p hp
      have hqb : b.factorization p / 3 ∈ greedyExponents := by
        simpa only [if_pos hspecial] using hb.2.2 p hp
      have hqc : c.factorization p / 3 ∈ greedyExponents := by
        simpa only [if_pos hspecial] using hc.2.2 p hp
      have hquot : a.factorization p / 3 + c.factorization p / 3 =
          b.factorization p / 3 + b.factorization p / 3 := by omega
      have hqAB := threeAPFree_greedyExponents hqa hqb hqc hquot
      omega
    · exact threeAPFree_greedyExponents
        (by simpa only [if_neg hspecial] using ha.2.2 p hp) (by simpa only [if_neg hspecial] using hb.2.2 p hp)
        (by simpa only [if_neg hspecial] using hc.2.2 p hp) h
  · simp [hp]

end OneDigitExchange

end GRHArticle.ProgressionFree
