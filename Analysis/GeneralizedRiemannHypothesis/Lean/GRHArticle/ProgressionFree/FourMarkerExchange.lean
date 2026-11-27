import GRHArticle.ProgressionFree.Rankin

/-!
# The four-marker exchange

This is the exact-valuation rule in the article's construction on primes up
to 1427. Its allowed marker exponents are `2, 5, 11, 14`. The rule is
progression-free on any family of satellite coordinates.
-/

namespace GRHArticle.ProgressionFree

/-- The four inserted valuations at the marker prime. -/
def fourMarkerExponents : Finset ℕ := {2, 5, 11, 14}

private theorem marker_pos {k : ℕ} (hk : k ∈ fourMarkerExponents) : 0 < k := by
  simp only [fourMarkerExponents, Finset.mem_insert, Finset.mem_singleton] at hk
  omega

private theorem marker_mod_three {k : ℕ} (hk : k ∈ fourMarkerExponents) : k % 3 = 2 := by
  simp only [fourMarkerExponents, Finset.mem_insert, Finset.mem_singleton] at hk
  omega

private theorem threeAPFree_fourMarkerExponents : ThreeAPFree (fourMarkerExponents : Set ℕ) := by
  decide

private theorem threeAPFree_inserted_satellite_digits :
    ThreeAPFree (({1, 2, 4} : Finset ℕ) : Set ℕ) := by
  decide

private theorem four_mem_greedyExponents : 4 ∈ greedyExponents :=
  (mem_greedyExponents_iff 4).mpr ⟨by decide, one_mem_greedyExponents⟩

private theorem greedy_triple_eq {a b c : ℕ}
    (ha : a ∈ greedyExponents) (hb : b ∈ greedyExponents) (hc : c ∈ greedyExponents)
    (h : a + c = b + b) : a = b ∧ b = c := by
  have hab := threeAPFree_greedyExponents ha hb hc h
  exact ⟨hab, by omega⟩

private theorem greedy_around_two {a c : ℕ}
    (ha : a ∈ greedyExponents) (hc : c ∈ greedyExponents) (h : a + c = 2 + 2) :
    (a = 0 ∧ c = 4) ∨ (a = 4 ∧ c = 0) ∨ (a = 1 ∧ c = 3) ∨ (a = 3 ∧ c = 1) := by
  have ha₀ := (mem_greedyExponents_iff a).mp ha |>.1
  have hc₀ := (mem_greedyExponents_iff c).mp hc |>.1
  omega

private theorem greedy_middle_for_endpoint_two {a b : ℕ}
    (ha : a ∈ greedyExponents) (hb : b ∈ greedyExponents) (h : a + 2 = b + b) :
    b = 1 ∨ b = 3 := by
  obtain ⟨ha₀, haq⟩ := (mem_greedyExponents_iff a).mp ha
  obtain ⟨hb₀, hbq⟩ := (mem_greedyExponents_iff b).mp hb
  have hcases : b % 3 = 0 ∨ b % 3 = 1 := by omega
  rcases hcases with hzero | hone
  · have hq : a / 3 + 1 = b / 3 + b / 3 := by omega
    obtain ⟨ha₁, haqq⟩ := (mem_greedyExponents_iff (a / 3)).mp haq
    obtain ⟨hb₁, hbqq⟩ := (mem_greedyExponents_iff (b / 3)).mp hbq
    have hd : b / 3 % 3 = 1 := by omega
    have hqq : 0 + a / 3 / 3 = b / 3 / 3 + b / 3 / 3 := by omega
    have hz := threeAPFree_greedyExponents zero_mem_greedyExponents hbqq haqq hqq
    exact Or.inr (by omega)
  · have hq : 0 + a / 3 = b / 3 + b / 3 := by omega
    have hz := threeAPFree_greedyExponents zero_mem_greedyExponents hbq haq hq
    exact Or.inl (by omega)

section ValuationVectors

variable {ι : Type*}

/-- The deleted old patterns. The exceptional coordinate in the second case
has value four, or has value three with a doubled marker from the insertions. -/
def fourMarkerDeleted (v : ℕ × (ι → ℕ)) : Prop :=
  ((∀ q, v.2 q = 1) ∧ 0 < v.1) ∨
  ∃ q, (∀ j, j ≠ q → v.2 j = 1) ∧
    (v.2 q = 4 ∨ (v.2 q = 3 ∧ ∃ k ∈ fourMarkerExponents, v.1 = 2 * k))

/-- Unchanged Rankin patterns that survive the four-marker deletions. -/
def fourMarkerKept (v : ℕ × (ι → ℕ)) : Prop :=
  v.1 ∈ greedyExponents ∧ (∀ q, v.2 q ∈ greedyExponents) ∧ ¬ fourMarkerDeleted v

/-- The inserted patterns with all satellite valuations one, or a single
satellite valuation raised to two or four. -/
def fourMarkerInserted (v : ℕ × (ι → ℕ)) : Prop :=
  v.1 ∈ fourMarkerExponents ∧ ((∀ q, v.2 q = 1) ∨
    ∃ q, (∀ j, j ≠ q → v.2 j = 1) ∧ (v.2 q = 2 ∨ v.2 q = 4))

/-- Allowed exact exponents at the marker and all satellites. -/
def fourMarkerExponentSet (ι : Type*) : Set (ℕ × (ι → ℕ)) :=
  {v | fourMarkerKept v ∨ fourMarkerInserted v}

private theorem kept_marker_zero {a : ℕ × (ι → ℕ)} (ha : fourMarkerKept a)
    (hones : ∀ q, a.2 q = 1) : a.1 = 0 :=
  Nat.eq_zero_of_not_pos fun hp => ha.2.2 (Or.inl ⟨hones, hp⟩)

private theorem kept_not_four {a : ℕ × (ι → ℕ)} (ha : fourMarkerKept a)
    (q : ι) (hones : ∀ j, j ≠ q → a.2 j = 1) (hfour : a.2 q = 4) : False :=
  ha.2.2 (Or.inr ⟨q, hones, Or.inl hfour⟩)

private theorem kept_not_three_double {a : ℕ × (ι → ℕ)} (ha : fourMarkerKept a)
    (q : ι) (hones : ∀ j, j ≠ q → a.2 j = 1) (hthree : a.2 q = 3)
    (k : ℕ) (hk : k ∈ fourMarkerExponents) (ha₂ : a.1 = 2 * k) : False :=
  ha.2.2 (Or.inr ⟨q, hones, Or.inr ⟨hthree, k, hk, ha₂⟩⟩)

private theorem inserted_satellite_digit {a : ℕ × (ι → ℕ)} (ha : fourMarkerInserted a)
    (q : ι) : a.2 q ∈ ({1, 2, 4} : Finset ℕ) := by
  rcases ha.2 with all | ⟨r, hother, hr⟩
  · simp [all q]
  · by_cases hqr : q = r
    · subst q
      rcases hr with h | h <;> simp [h]
    · simp [hother q hqr]

private theorem no_one_inserted_end {a b c : ℕ × (ι → ℕ)}
    (ha : fourMarkerKept a) (hb : fourMarkerKept b) (hc : fourMarkerInserted c)
    (h : a + c = b + b) : False := by
  have hmarker : a.1 + c.1 = b.1 + b.1 := congrArg Prod.fst h
  have hsat (q : ι) : a.2 q + c.2 q = b.2 q + b.2 q :=
    congrArg (fun v : ℕ × (ι → ℕ) => v.2 q) h
  have hk := marker_pos hc.1
  have hold (q : ι) (hg : c.2 q ∈ greedyExponents) :
      a.2 q = c.2 q ∧ b.2 q = c.2 q := by
    obtain ⟨hab, hbc⟩ := greedy_triple_eq (ha.2.1 q) (hb.2.1 q) hg (hsat q)
    exact ⟨hab.trans hbc, hbc⟩
  have hones (q : ι) (hq : c.2 q = 1) : a.2 q = 1 ∧ b.2 q = 1 := by
    simpa only [hq] using hold q (hq ▸ one_mem_greedyExponents)
  rcases hc.2 with hall | ⟨q, hother, hq | hq⟩
  · have hb₀ := kept_marker_zero hb (fun j => (hones j (hall j)).2)
    omega
  · have hqeq : a.2 q + 2 = b.2 q + b.2 q := by simpa only [hq] using hsat q
    rcases greedy_middle_for_endpoint_two (ha.2.1 q) (hb.2.1 q) hqeq with h₁ | h₃
    · have hb₀ := kept_marker_zero hb (fun j => by
        by_cases hj : j = q
        · exact hj ▸ h₁
        · exact (hones j (hother j hj)).2)
      omega
    · exact kept_not_four ha q (fun j hj => (hones j (hother j hj)).1) (by omega)
  · have hfour := (hold q (hq ▸ four_mem_greedyExponents)).1.trans hq
    exact kept_not_four ha q (fun j hj => (hones j (hother j hj)).1) hfour

private theorem no_one_inserted_middle {a b c : ℕ × (ι → ℕ)}
    (ha : fourMarkerKept a) (hb : fourMarkerInserted b) (hc : fourMarkerKept c)
    (h : a + c = b + b) : False := by
  have hmarker : a.1 + c.1 = b.1 + b.1 := congrArg Prod.fst h
  have hsat (q : ι) : a.2 q + c.2 q = b.2 q + b.2 q :=
    congrArg (fun v : ℕ × (ι → ℕ) => v.2 q) h
  have hk := marker_pos hb.1
  have hold (q : ι) (hg : b.2 q ∈ greedyExponents) :
      a.2 q = b.2 q ∧ c.2 q = b.2 q := by
    obtain ⟨hab, hbc⟩ := greedy_triple_eq (ha.2.1 q) hg (hc.2.1 q) (hsat q)
    exact ⟨hab, hbc.symm⟩
  have hones (q : ι) (hq : b.2 q = 1) : a.2 q = 1 ∧ c.2 q = 1 := by
    simpa only [hq] using hold q (hq ▸ one_mem_greedyExponents)
  rcases hb.2 with hall | ⟨q, hother, hq | hq⟩
  · have ha₀ := kept_marker_zero ha (fun j => (hones j (hall j)).1)
    have hc₀ := kept_marker_zero hc (fun j => (hones j (hall j)).2)
    omega
  · have hqeq : a.2 q + c.2 q = 2 + 2 := by simpa only [hq] using hsat q
    have haones (j : ι) (hj : j ≠ q) : a.2 j = 1 := (hones j (hother j hj)).1
    have hcones (j : ι) (hj : j ≠ q) : c.2 j = 1 := (hones j (hother j hj)).2
    rcases greedy_around_two (ha.2.1 q) (hc.2.1 q) hqeq with
      ⟨_, hc₄⟩ | ⟨ha₄, _⟩ | ⟨ha₁, hc₃⟩ | ⟨ha₃, hc₁⟩
    · exact kept_not_four hc q hcones hc₄
    · exact kept_not_four ha q haones ha₄
    · have ha₀ := kept_marker_zero ha (fun j => by
        by_cases hj : j = q
        · exact hj ▸ ha₁
        · exact haones j hj)
      exact kept_not_three_double hc q hcones hc₃ b.1 hb.1 (by omega)
    · have hc₀ := kept_marker_zero hc (fun j => by
        by_cases hj : j = q
        · exact hj ▸ hc₁
        · exact hcones j hj)
      exact kept_not_three_double ha q haones ha₃ b.1 hb.1 (by omega)
  · have hfour := (hold q (hq ▸ four_mem_greedyExponents)).1.trans hq
    exact kept_not_four ha q (fun j hj => (hones j (hother j hj)).1) hfour

private theorem no_two_inserted_ends {a b c : ℕ × (ι → ℕ)}
    (ha : fourMarkerInserted a) (hb : fourMarkerKept b) (hc : fourMarkerInserted c)
    (h : a + c = b + b) : False := by
  have hmarker : a.1 + c.1 = b.1 + b.1 := congrArg Prod.fst h
  have ha₂ := marker_mod_three ha.1
  have hb₀ := (mem_greedyExponents_iff b.1).mp hb.1 |>.1
  have hc₂ := marker_mod_three hc.1
  omega

private theorem no_two_inserted_adjacent {a b c : ℕ × (ι → ℕ)}
    (ha : fourMarkerKept a) (hb : fourMarkerInserted b) (hc : fourMarkerInserted c)
    (h : a + c = b + b) : False := by
  have hmarker : a.1 + c.1 = b.1 + b.1 := congrArg Prod.fst h
  have ha₀ := (mem_greedyExponents_iff a.1).mp ha.1 |>.1
  have hb₂ := marker_mod_three hb.1
  have hc₂ := marker_mod_three hc.1
  omega

/-- The actual four-marker exact-valuation rule contains no nonconstant
three-term arithmetic progression. -/
theorem threeAPFree_fourMarkerExponentSet (ι : Type*) :
    ThreeAPFree (fourMarkerExponentSet ι) := by
  intro a ha b hb c hc h
  have hmarker : a.1 + c.1 = b.1 + b.1 := congrArg Prod.fst h
  have hsat (q : ι) : a.2 q + c.2 q = b.2 q + b.2 q :=
    congrArg (fun v : ℕ × (ι → ℕ) => v.2 q) h
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact Prod.ext (threeAPFree_greedyExponents ha.1 hb.1 hc.1 hmarker)
      (funext fun q => threeAPFree_greedyExponents (ha.2.1 q) (hb.2.1 q) (hc.2.1 q) (hsat q))
  · exact (no_one_inserted_end ha hb hc h).elim
  · exact (no_one_inserted_middle ha hb hc h).elim
  · exact (no_two_inserted_adjacent ha hb hc h).elim
  · exact (no_one_inserted_end hc hb ha (by simpa only [add_comm] using h)).elim
  · exact (no_two_inserted_ends ha hb hc h).elim
  · exact (no_two_inserted_adjacent hc hb ha (by simpa only [add_comm] using h)).elim
  · exact Prod.ext (threeAPFree_fourMarkerExponents ha.1 hb.1 hc.1 hmarker)
      (funext fun q => threeAPFree_inserted_satellite_digits
        (inserted_satellite_digit ha q) (inserted_satellite_digit hb q)
        (inserted_satellite_digit hc q) (hsat q))

end ValuationVectors

/-- The exact four-marker exchange on a finite set of satellite primes. All
other prime valuations continue to obey the Rankin rule. -/
def fourMarkerExchangeSet (S : Finset ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧
    (n.factorization 2, fun p : ↥S => n.factorization p.val) ∈ fourMarkerExponentSet ↥S ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ S → n.factorization p ∈ greedyExponents}

/-- The actual four-marker exchange is progression-free for rational ratios. -/
theorem threeGPFree_fourMarkerExchangeSet (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ThreeGPFree (fourMarkerExchangeSet S) := by
  intro a ha b hb c hc habc
  have hval := (mul_eq_mul_iff_prime_exponents ha.1 hb.1 hc.1).mp habc
  have htuple :=
    threeAPFree_fourMarkerExponentSet ↥S ha.2.1 hb.2.1 hc.2.1
      (Prod.ext (hval 2 Nat.prime_two) (funext fun p => hval p.val (hS p.val p.property)))
  apply Nat.factorization_inj ha.1 hb.1
  ext p
  by_cases hp : p.Prime
  · by_cases hp₂ : p = 2
    · subst p
      exact congrArg (fun v : ℕ × (↥S → ℕ) => v.1) htuple
    · by_cases hpS : p ∈ S
      · exact congrArg (fun v : ℕ × (↥S → ℕ) => v.2 ⟨p, hpS⟩) htuple
      · exact threeAPFree_greedyExponents (ha.2.2 p hp hp₂ hpS) (hb.2.2 p hp hp₂ hpS)
          (hc.2.2 p hp hp₂ hpS) (hval p hp)
  · simp [hp]

/-- The exact progression-freeness assertion for the primes up to 1427. -/
theorem threeGPFree_fourMarkerExchange1427 :
    ThreeGPFree (fourMarkerExchangeSet ((Nat.primesLE 1427).erase 2)) :=
  threeGPFree_fourMarkerExchangeSet _ fun _ h => Nat.prime_of_mem_primesLE (Finset.mem_of_mem_erase h)

end GRHArticle.ProgressionFree
