import ExponentialIdentities.TwoBaseIntegerExponent

/-!
# Prime-log-product independence implies the two-base conjecture

Expanding a hypothetical counterexample over prime factorizations turns the defining relation
into an *integer-coefficient linear form in products of two prime logarithms*.  Concretely, a
counterexample is a pair of positive naturals `M = 2 ^ x`, `A = 3 ^ x` with

`log M * log 3 = log A * log 2`,

and writing `M = ∏ p ^ α p`, `A = ∏ p ^ γ p` this says

`∑ p, α p * (log p * log 3) - ∑ p, γ p * (log p * log 2) = 0`.

Collecting coefficients in the family `{log p * log q}` of products of two prime logarithms,
the unordered pair `{p, 3}` receives `α p`, the pair `{p, 2}` receives `-γ p`, the pair
`{3, 3}` receives `α 3`, the pair `{2, 2}` receives `-γ 2`, and `{2, 3}` receives
`α 2 - γ 3`.  Hence, if products of two prime logarithms are linearly independent over `ℚ`,
every one of those coefficients vanishes, forcing `M = 2 ^ n` and therefore `x = n ∈ ℤ`.

This gives a sufficient condition for the Alaoglu--Erdős conjecture which is *different* from
the four exponentials conjecture: it is a statement purely about `ℚ`-linear independence of
the numbers `log p * log q`, itself a consequence of Schanuel's conjecture but not known
unconditionally --- indeed even the irrationality of `(log 3) ^ 2 / (log 2) ^ 2` is open.

The main theorem `alaogluErdosConjecture_of_primeLogProductIndependence` is unconditional
Lean: the independence assumption appears only as an explicit hypothesis.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- The logarithm of a positive natural number, expanded over its prime factorization. -/
theorem log_natCast_eq_sum_primeFactors {n : ℕ} (hn : n ≠ 0) :
    Real.log n = ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log p := by
  have hcast : (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) := by
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.prod_primeFactors_pow_factorization hn)
  have hne : ∀ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ≠ 0 := by
    intro p hp
    have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    positivity
  rw [hcast, Real.log_prod hne]
  exact Finset.sum_congr rfl fun p _ ↦ Real.log_pow _ _

/-- **Prime-log-product independence.**  The assertion that the products `log p * log q` of
two prime logarithms are linearly independent over `ℚ`, stated in the equivalent
integer-coefficient form: whenever an integer combination indexed by ordered pairs of primes
vanishes, its symmetrization vanishes coefficientwise.  (For `p = q` the conclusion reads
`2 * c p p = 0`, i.e. `c p p = 0`.)

This is an open statement; it follows from Schanuel's conjecture.  It is recorded here as a
`Prop`, never asserted. -/
def PrimeLogProductIndependence : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℕ → ℤ),
    (∀ p ∈ S, Nat.Prime p) →
    (∑ p ∈ S, ∑ q ∈ S, (c p q : ℝ) * (Real.log p * Real.log q)) = 0 →
    ∀ p ∈ S, ∀ q ∈ S, c p q + c q p = 0

/-- The coefficient family attached to a hypothetical counterexample with outputs `M` and
`A`: the pair `(p, 3)` carries the exponent of `p` in `M`, and the pair `(p, 2)` carries
minus the exponent of `p` in `A`. -/
private def counterexampleCoeff (M A : ℕ) (p q : ℕ) : ℤ :=
  (if q = 3 then (M.factorization p : ℤ) else 0) -
    (if q = 2 then (A.factorization p : ℤ) else 0)

/-- **Prime-log-product independence implies the Alaoglu--Erdős conjecture.** -/
theorem alaogluErdosConjecture_of_primeLogProductIndependence
    (hind : PrimeLogProductIndependence) : AlaogluErdosConjecture := by
  classical
  intro x h₂ h₃
  -- Extract the two integral outputs as natural numbers.
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer h₂
  obtain ⟨zM, hzM⟩ := h₂
  obtain ⟨zA, hzA⟩ := h₃
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  have hzMpos : 0 < zM := by exact_mod_cast (hzM ▸ h2pos)
  have hzApos : 0 < zA := by exact_mod_cast (hzA ▸ h3pos)
  lift zM to ℕ using hzMpos.le with M hMcast
  lift zA to ℕ using hzApos.le with A hAcast
  have hM0 : M ≠ 0 := by
    have : 0 < M := by exact_mod_cast hzMpos
    omega
  have hA0 : A ≠ 0 := by
    have : 0 < A := by exact_mod_cast hzApos
    omega
  have hMval : (M : ℝ) = (2 : ℝ) ^ x := by exact_mod_cast hzM
  have hAval : (A : ℝ) = (3 : ℝ) ^ x := by exact_mod_cast hzA
  -- The defining logarithmic relation.
  have hlogM : Real.log M = x * Real.log 2 := by
    rw [hMval, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hlogA : Real.log A = x * Real.log 3 := by
    rw [hAval, Real.log_rpow (by norm_num : (0 : ℝ) < 3)]
  have hrel : Real.log M * Real.log 3 - Real.log A * Real.log 2 = 0 := by
    rw [hlogM, hlogA]; ring
  -- The finite set of primes involved.
  set S : Finset ℕ := M.primeFactors ∪ A.primeFactors ∪ {2, 3} with hS
  have h2S : (2 : ℕ) ∈ S := by simp [hS]
  have h3S : (3 : ℕ) ∈ S := by simp [hS]
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    simp only [hS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with (hp | hp) | hp
    · exact Nat.prime_of_mem_primeFactors hp
    · exact Nat.prime_of_mem_primeFactors hp
    · rcases hp with rfl | rfl
      · norm_num
      · norm_num
  -- Rewrite the relation as a vanishing integer combination of prime-log products.
  set c : ℕ → ℕ → ℤ := counterexampleCoeff M A with hc
  have hinner : ∀ p : ℕ, (∑ q ∈ S, (c p q : ℝ) * (Real.log p * Real.log q)) =
      (M.factorization p : ℝ) * (Real.log p * Real.log 3) -
        (A.factorization p : ℝ) * (Real.log p * Real.log 2) := by
    intro p
    have hsub : ({2, 3} : Finset ℕ) ⊆ S := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact h2S
      · exact h3S
    have hzero : ∀ q ∈ S, q ∉ ({2, 3} : Finset ℕ) →
        (c p q : ℝ) * (Real.log p * Real.log q) = 0 := by
      intro q _ hq
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
      have : c p q = 0 := by
        simp [hc, counterexampleCoeff, hq.1, hq.2]
      rw [this]
      simp
    rw [← Finset.sum_subset hsub hzero]
    rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
    have hc2 : c p 2 = -(A.factorization p : ℤ) := by
      simp [hc, counterexampleCoeff]
    have hc3 : c p 3 = (M.factorization p : ℤ) := by
      simp [hc, counterexampleCoeff]
    rw [hc2, hc3]
    push_cast
    ring
  have houter : (∑ p ∈ S, ∑ q ∈ S, (c p q : ℝ) * (Real.log p * Real.log q)) = 0 := by
    have hMsum : (∑ p ∈ S, (M.factorization p : ℝ) * Real.log p) = Real.log M := by
      rw [log_natCast_eq_sum_primeFactors hM0]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro p hp
        simp only [hS, Finset.mem_union]
        exact Or.inl (Or.inl hp)
      · intro p _ hp
        have : M.factorization p = 0 := by
          by_contra hne
          exact hp (Nat.support_factorization (n := M) ▸ Finsupp.mem_support_iff.mpr hne)
        rw [this]
        simp
    have hAsum : (∑ p ∈ S, (A.factorization p : ℝ) * Real.log p) = Real.log A := by
      rw [log_natCast_eq_sum_primeFactors hA0]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro p hp
        simp only [hS, Finset.mem_union]
        exact Or.inl (Or.inr hp)
      · intro p _ hp
        have : A.factorization p = 0 := by
          by_contra hne
          exact hp (Nat.support_factorization (n := A) ▸ Finsupp.mem_support_iff.mpr hne)
        rw [this]
        simp
    calc (∑ p ∈ S, ∑ q ∈ S, (c p q : ℝ) * (Real.log p * Real.log q))
        = ∑ p ∈ S, ((M.factorization p : ℝ) * (Real.log p * Real.log 3) -
            (A.factorization p : ℝ) * (Real.log p * Real.log 2)) :=
          Finset.sum_congr rfl fun p _ ↦ hinner p
      _ = (∑ p ∈ S, (M.factorization p : ℝ) * Real.log p) * Real.log 3 -
            (∑ p ∈ S, (A.factorization p : ℝ) * Real.log p) * Real.log 2 := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
          congr 1 <;> exact Finset.sum_congr rfl fun p _ ↦ by ring
      _ = Real.log M * Real.log 3 - Real.log A * Real.log 2 := by rw [hMsum, hAsum]
      _ = 0 := hrel
  -- Apply the independence hypothesis.
  have hvanish := hind S c hSprime houter
  -- Every prime other than `2` is absent from `M`.
  have hMfact : ∀ p : ℕ, p ≠ 2 → M.factorization p = 0 := by
    intro p hp2
    by_cases hpS : p ∈ S
    · by_cases hp3 : p = 3
      · -- diagonal pair `{3, 3}`
        have h := hvanish p hpS p hpS
        have hcpp : c p p = (M.factorization p : ℤ) := by
          simp [hc, counterexampleCoeff, hp3]
        rw [hcpp] at h
        omega
      · -- pair `{p, 3}` with `p ∉ {2, 3}`
        have h := hvanish p hpS 3 h3S
        have hcp3 : c p 3 = (M.factorization p : ℤ) := by
          simp [hc, counterexampleCoeff]
        have hc3p : c 3 p = 0 := by
          simp [hc, counterexampleCoeff, hp2, hp3]
        rw [hcp3, hc3p] at h
        omega
    · -- primes outside `S` do not divide `M`
      by_contra hne
      exact hpS (by
        simp only [hS, Finset.mem_union]
        exact Or.inl (Or.inl (Nat.support_factorization (n := M) ▸
          Finsupp.mem_support_iff.mpr hne)))
  -- Hence `M` is a power of two.
  have hMsingle : M.factorization = Finsupp.single 2 (M.factorization 2) := by
    ext p
    by_cases hp : p = 2
    · subst hp; simp
    · rw [hMfact p hp, Finsupp.single_apply, if_neg (Ne.symm hp)]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M = 2 ^ n :=
    ⟨M.factorization 2, Nat.eq_pow_of_factorization_eq_single hM0 hMsingle⟩
  -- Therefore the exponent is that integer.
  refine ⟨n, ?_⟩
  have hxn : x = (n : ℝ) := by
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    show (2 : ℝ) ^ x = (2 : ℝ) ^ (n : ℝ)
    rw [← hMval, hn, Real.rpow_natCast]
    push_cast
    ring
  rw [hxn]
  push_cast
  ring

end LeanProofs.TwoBaseIntegerExponent
