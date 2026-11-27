import GRHArticle.ProgressionFree.SharedDeletionProgressions

/-!
# Shared-deletion block rules for positive integers

Prime exponents of a rational-ratio progression vary affinely with integral
steps. The edited block rule and the independent exponent rules outside it
therefore force every prime exponent to be constant.
-/

namespace GRHArticle.ProgressionFree

/-- The absence of nonconstant geometric progressions with positive rational
ratio. Both increasing and decreasing orders are allowed. -/
def KTermGPFree (k : ℕ) (A : Set ℕ) : Prop :=
  ∀ (a : Fin k → ℕ) (u r : ℚ), 0 < u → 0 < r → (∀ i, a i ∈ A) →
    (∀ i, (a i : ℚ) = u*r^i.val) → r = 1

/-- Each valuation of a rational geometric progression is an integral affine
string. Vanishing of the steps at every prime forces ratio one. -/
theorem exists_primeExponentAffine {k : ℕ} (hk : 2 ≤ k) {a : Fin k → ℕ}
    (ha : ∀ i, a i ≠ 0) {u r : ℚ} (hu : 0 < u)
    (hf : ∀ i, (a i : ℚ) = u*r^i.val) :
    ∃ v d : ℕ → ℤ, (∀ i p, ((a i).factorization p : ℤ) = v p + (i.val : ℤ)*d p) ∧
      ((∀ p : ℕ, p.Prime → d p = 0) → r = 1) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  have h0 : (a i₀ : ℚ) = u := by simpa [i₀] using hf i₀
  have h1 : (a i₁ : ℚ) = u*r := by simpa [i₁] using hf i₁
  let v (p : ℕ) : ℤ := (a i₀).factorization p
  let d (p : ℕ) : ℤ := ((a i₁).factorization p : ℤ) - v p
  refine ⟨v, d, ?_, ?_⟩
  · intro i p
    have he : a i * (a i₀)^i.val = a i₀ * (a i₁)^i.val := by
      suffices (a i : ℚ) * (a i₀ : ℚ)^i.val = (a i₀ : ℚ) * (a i₁ : ℚ)^i.val by
        exact_mod_cast this
      rw [hf i, h0, h1, mul_pow]
      ring
    have hp := congrArg (fun n : ℕ ↦ n.factorization p) he
    simp only [Nat.factorization_mul (ha i) (pow_ne_zero _ (ha i₀)),
      Nat.factorization_mul (ha i₀) (pow_ne_zero _ (ha i₁)),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hp
    have hZ : ((a i).factorization p : ℤ) + (i.val : ℤ)*(a i₀).factorization p =
        ((a i₀).factorization p : ℤ) + (i.val : ℤ)*(a i₁).factorization p := by
      exact_mod_cast hp
    dsimp [v, d]
    linear_combination hZ
  · intro h
    have h01 : a i₁ = a i₀ := by
      apply Nat.factorization_inj (ha i₁) (ha i₀)
      ext p
      by_cases hp : p.Prime
      · have hh := h p hp
        dsimp [d, v] at hh
        exact_mod_cast sub_eq_zero.mp hh
      · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
          Nat.factorization_eq_zero_of_not_prime _ hp]
    rw [h01, h0] at h1
    exact (mul_left_cancel₀ (ne_of_gt hu) (by simpa only [mul_one] using h1.symm :
      u*r = u*1))

/-- The independently prescribed exponent rule on all primes. -/
def integerIndependentExponentSet (G : Set ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ ∀ p : ℕ, p.Prime → n.factorization p ∈ G}

theorem kTermGPFree_integerIndependentExponentSet {k : ℕ} (hk : 2 ≤ k) {G : Set ℕ}
    (hG : KTermAPFree k G) : KTermGPFree k (integerIndependentExponentSet G) := by
  intro a u r hu _ ha hf
  obtain ⟨v,d,hAffine,hone⟩ := exists_primeExponentAffine hk (fun i ↦ (ha i).1) hu hf
  exact hone fun p hp ↦ hG _ (v p) (d p) (fun i ↦ (ha i).2 p hp) (fun i ↦ hAffine i p)

/-- The prime tested by each coordinate of the article's marker-and-satellite block. -/
def sharedDeletionPrime (marker : ℕ) (B : Finset ℕ) : Option ↥B → ℕ
  | none => marker
  | some q => q.val

/-- The article's shared-deletion rule on one prime block and the independent
exponent rule at all other primes. -/
def integerSharedDeletionSet (k : ℕ) (G : Set ℕ) (marker : ℕ) (B : Finset ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧
    (fun p ↦ n.factorization (sharedDeletionPrime marker B p)) ∈ sharedDeletionRule (k-2) G ∧
    ∀ p : ℕ, p.Prime → p ≠ marker → p ∉ B → n.factorization p ∈ G}

/-- The edited block gives an actual positive-integer progression-free set
for every length, including progressions of nonintegral rational ratio. -/
theorem kTermGPFree_integerSharedDeletionSet {k : ℕ} (hk : 3 ≤ k) {G : Set ℕ}
    (hG : KTermAPFree k G) (hb : k-2 ∈ G) (hnext : k-2+1 ∉ G)
    (marker : ℕ) (B : Finset ℕ) : KTermGPFree k (integerSharedDeletionSet k G marker B) := by
  intro a u r hu _ ha hf
  obtain ⟨v,d,hAffine,hone⟩ :=
    exists_primeExponentAffine (by omega) (fun i ↦ (ha i).1) hu hf
  have hblock : ∀ p, d (sharedDeletionPrime marker B p) = 0 :=
    sharedDeletionRule_step_zero hk hG hb hnext (fun i ↦ (ha i).2.1)
      (fun i p ↦ hAffine i (sharedDeletionPrime marker B p))
  apply hone
  intro p hp
  by_cases hpm : p = marker
  · simpa only [hpm, sharedDeletionPrime] using hblock none
  by_cases hpB : p ∈ B
  · exact hblock (some ⟨p,hpB⟩)
  · exact hG _ (v p) (d p) (fun i ↦ (ha i).2.2 p hp hpm hpB) (fun i ↦ hAffine i p)

end GRHArticle.ProgressionFree
