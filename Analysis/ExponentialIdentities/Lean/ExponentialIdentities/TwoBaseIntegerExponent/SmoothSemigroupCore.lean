import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Finite cores of the Bhargava calculus for the two–three semigroup

Two kernel-checked ingredients of the Bhargava-factorial analysis of
`𝓑 = {2^a 3^b : a, b ≥ 0}`:

* **Pigeonhole cutoff.**  If a finite set of distinct positive integers below `B` has fewer
  residues modulo `m` than elements, then `m < B`.  Applied to the `(R+1)²` box elements
  `2^a 3^b ≤ 6^R`, this is the square-box cutoff: any modulus whose two–three orbit has at
  most `k < (R+1)²` elements satisfies `m < 6^R`, which makes the generalized factorial
  `k!_𝓑` finitely computable.
* **Consecutive triples.**  The only triples of consecutive `3`-smooth integers are
  `{1,2,3}` and `{2,3,4}`.  This is the decisive step in the first-defect theorem
  (`Q_𝓑(E) ≥ 7` for six nodes): the sole gap pattern that could beat `7` would need two
  consecutive triples four units apart.
-/

namespace LeanProofs.TwoBaseIntegerExponent.SmoothSemigroup

open Finset

/-! ### The pigeonhole cutoff -/

/-- If a finite set of distinct positive integers below `B` occupies fewer than `s.card`
residues modulo `m`, then `m < B`. -/
theorem modulus_lt_of_card_image_lt {s : Finset ℕ} {m B : ℕ}
    (hB : ∀ x ∈ s, 0 < x ∧ x ≤ B) (hcard : (s.image (· % m)).card < s.card) : m < B := by
  classical
  -- Two distinct elements share a residue.
  obtain ⟨x, hx, y, hy, hxy, hmod⟩ : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x % m = y % m := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (· % m) s := fun a ha b hb hab => by
      by_contra hne
      exact absurd hab (hcon a ha b hb hne)
    have := Finset.card_image_of_injOn hinj
    omega
  -- Order them and take the difference.
  wlog hlt : y < x generalizing x y
  · exact this y hy x hx hxy.symm hmod.symm (by omega)
  have hdvd : m ∣ x - y := by
    have hmodz : (x : ℤ) % m = (y : ℤ) % m := by exact_mod_cast hmod
    have hzmod : ((x : ℤ) - y) % m = 0 := by
      rw [Int.sub_emod, hmodz, sub_self, Int.zero_emod]
    have hdvdz : (m : ℤ) ∣ (x : ℤ) - y := Int.dvd_of_emod_eq_zero hzmod
    have hcast : ((x - y : ℕ) : ℤ) = (x : ℤ) - y := Nat.cast_sub hlt.le
    have : (m : ℤ) ∣ ((x - y : ℕ) : ℤ) := by rwa [hcast]
    exact_mod_cast this
  have hpos : 0 < x - y := by omega
  have hxB := (hB x hx).2
  have hyB := (hB y hy).1
  have : m ≤ x - y := Nat.le_of_dvd hpos hdvd
  omega

/-- Injectivity of `(a, b) ↦ 2^a 3^b`. -/
theorem two_pow_mul_three_pow_injective {a b c d : ℕ} (h : 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d) :
    a = c ∧ b = d := by
  have key : ∀ x y : ℕ, ∀ p : ℕ,
      (2 ^ x * 3 ^ y).factorization p
        = x * (Nat.factorization 2) p + y * (Nat.factorization 3) p := by
    intro x y p
    rw [Nat.factorization_mul (pow_ne_zero x (by norm_num)) (pow_ne_zero y (by norm_num)),
      Nat.factorization_pow, Nat.factorization_pow]
    simp
  have h2 := congrArg (fun n : ℕ => n.factorization 2) h
  have h3 := congrArg (fun n : ℕ => n.factorization 3) h
  simp only [key] at h2 h3
  have f22 : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have f33 : (Nat.factorization 3) 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
  have f32 : (Nat.factorization 3) 2 = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]; omega
  have f23 : (Nat.factorization 2) 3 = 0 := by
    rw [Nat.factorization_eq_zero_of_not_dvd]; omega
  rw [f22, f32] at h2
  rw [f33, f23] at h3
  omega

/-- **Square-box cutoff.**  If the box `{2^a 3^b : a, b ≤ R}` occupies at most
`k < (R+1)²` residues modulo `m`, then `m < 6^R` (for `R ≥ 1`). -/
theorem smooth_box_cutoff {m R k : ℕ}
    (hcard : (((range (R + 1)) ×ˢ (range (R + 1))).image
      (fun p : ℕ × ℕ => (2 ^ p.1 * 3 ^ p.2) % m)).card ≤ k)
    (hk : k < (R + 1) ^ 2) : m < 6 ^ R := by
  classical
  set box : Finset ℕ := ((range (R + 1)) ×ˢ (range (R + 1))).image
    (fun p : ℕ × ℕ => 2 ^ p.1 * 3 ^ p.2) with hbox
  have hboxcard : box.card = (R + 1) ^ 2 := by
    rw [hbox, Finset.card_image_of_injOn]
    · rw [Finset.card_product, Finset.card_range]; ring
    · intro p hp q hq hpq
      obtain ⟨h1, h2⟩ := two_pow_mul_three_pow_injective hpq
      exact Prod.ext h1 h2
  have himage : (box.image (· % m)).card ≤ k := by
    rw [hbox, Finset.image_image]
    exact hcard
  apply modulus_lt_of_card_image_lt (s := box) (B := 6 ^ R)
  · intro x hx
    rw [hbox, Finset.mem_image] at hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    constructor
    · positivity
    · calc 2 ^ a * 3 ^ b ≤ 2 ^ R * 3 ^ R := by
            exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega))
              (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 6 ^ R := by rw [← Nat.mul_pow]
  · omega

/-! ### Consecutive three-smooth triples -/

/-- `n` is `3`-smooth: a product of a power of two and a power of three. -/
def IsThreeSmooth (n : ℕ) : Prop := ∃ a b : ℕ, n = 2 ^ a * 3 ^ b

/-- An odd `3`-smooth number is a power of `3`. -/
theorem odd_threeSmooth {n : ℕ} (h : IsThreeSmooth n) (hodd : n % 2 = 1) :
    ∃ b : ℕ, n = 3 ^ b := by
  obtain ⟨a, b, rfl⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨b, by rw [pow_zero, one_mul]⟩
  · exfalso
    have : 2 ∣ 2 ^ a * 3 ^ b := Dvd.dvd.mul_right (dvd_pow_self 2 ha.ne') _
    omega

/-- Powers of two differing by two: `2^a + 2 = 2^c` forces `(a, c) = (1, 2)`. -/
theorem pow_two_add_two {a c : ℕ} (h : 2 ^ a + 2 = 2 ^ c) : a = 1 ∧ c = 2 := by
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · -- `3 = 2^c`
      exfalso
      rcases Nat.lt_or_ge c 2 with hc | hc
      · interval_cases c <;> omega
      · have : 2 ^ 2 ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc
        omega
    · -- `4 = 2^c` gives `c = 2`
      constructor
      · rfl
      · rcases Nat.lt_or_ge c 3 with hc | hc
        · interval_cases c <;> omega
        · exfalso
          have : 2 ^ 3 ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) hc
          omega
  · -- `a ≥ 2`: left side is `2 (mod 4)`, so `c = 1`, contradiction.
    exfalso
    have h4 : 4 ∣ 2 ^ a := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
      simpa using this
    have hc2 : ¬ 4 ∣ 2 ^ c := by omega
    have hc : c < 2 := by
      by_contra hge
      exact hc2 (by simpa using Nat.pow_dvd_pow 2 (by omega : 2 ≤ c))
    have hpos : 0 < 2 ^ a := by positivity
    interval_cases c <;> omega

/-- Powers of three differing by two: `3^b + 2 = 3^c` forces `(b, c) = (0, 1)`. -/
theorem pow_three_add_two {b c : ℕ} (h : 3 ^ b + 2 = 3 ^ c) : b = 0 ∧ c = 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · constructor
    · rfl
    · -- `3 = 3^c`
      rcases Nat.lt_or_ge c 2 with hc | hc
      · interval_cases c <;> omega
      · exfalso
        have : 3 ^ 2 ≤ 3 ^ c := Nat.pow_le_pow_right (by omega) hc
        omega
  · exfalso
    have hcpos : 0 < c := by
      by_contra hc
      have : c = 0 := by omega
      subst this
      have : 3 ≤ 3 ^ b := by
        calc 3 = 3 ^ 1 := (pow_one 3).symm
          _ ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) hb
      omega
    have h3b : 3 ∣ 3 ^ b := dvd_pow_self 3 hb.ne'
    have h3c : 3 ∣ 3 ^ c := dvd_pow_self 3 hcpos.ne'
    omega

/-- **Consecutive triples.**  If `t, t+1, t+2` are all `3`-smooth and `t ≥ 1`, then `t = 1`
or `t = 2`: the only consecutive triples in the two–three semigroup are `{1,2,3}` and
`{2,3,4}`. -/
theorem consecutive_threeSmooth_triples {t : ℕ} (ht : 1 ≤ t)
    (h0 : IsThreeSmooth t) (h1 : IsThreeSmooth (t + 1)) (h2 : IsThreeSmooth (t + 2)) :
    t = 1 ∨ t = 2 := by
  rcases Nat.mod_two_eq_zero_or_one t with he | ho
  · -- `t` even: `t+1` odd, `t+1 = 3^b` with `b ≥ 1`, so `3 ∤ t, t+2`; both are powers of 2.
    right
    obtain ⟨b, hb⟩ := odd_threeSmooth h1 (by omega)
    have hb1 : b ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hb
      omega
    have h3mid : 3 ∣ t + 1 := by rw [hb]; exact dvd_pow_self 3 hb1
    have hpow : ∀ n, IsThreeSmooth n → ¬ 3 ∣ n → ∃ a, n = 2 ^ a := by
      rintro n ⟨a, b', rfl⟩ h3
      rcases Nat.eq_zero_or_pos b' with rfl | hbpos
      · exact ⟨a, by rw [pow_zero, mul_one]⟩
      · exact absurd (Dvd.dvd.mul_left (dvd_pow_self 3 hbpos.ne') _) h3
    have h3t : ¬ 3 ∣ t := by intro hd; omega
    have h3t2 : ¬ 3 ∣ (t + 2) := by intro hd; omega
    obtain ⟨a₀, ha₀⟩ := hpow t h0 h3t
    obtain ⟨a₂, ha₂⟩ := hpow (t + 2) h2 h3t2
    have hkey := pow_two_add_two (a := a₀) (c := a₂) (by omega)
    rw [hkey.1, pow_one] at ha₀
    omega
  · -- `t` odd: `t` and `t+2` are powers of three differing by two.
    left
    obtain ⟨b₀, hb₀⟩ := odd_threeSmooth h0 (by omega)
    obtain ⟨b₂, hb₂⟩ := odd_threeSmooth h2 (by omega)
    have hkey := pow_three_add_two (b := b₀) (c := b₂) (by omega)
    rw [hkey.1, pow_zero] at hb₀
    omega


/-! ### Consecutive three-smooth pairs (Catalan-free) -/

/-- `2^a = 3^b + 1` forces `(a, b) = (1, 0)` or `(2, 1)`. -/
theorem pow_two_eq_pow_three_add_one {a b : ℕ} (h : 2 ^ a = 3 ^ b + 1) :
    (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · left
    refine ⟨?_, rfl⟩
    rw [pow_zero] at h
    have hpos : 0 < 2 ^ a := by positivity
    rcases Nat.lt_or_ge a 2 with ha | ha
    · interval_cases a <;> omega
    · exfalso
      have : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
      omega
  · right
    -- `a` is even: reduce modulo 3.
    have haeven : Even a := by
      rcases Nat.even_or_odd a with he | ho
      · exact he
      · exfalso
        obtain ⟨e, he⟩ := ho
        subst he
        have h4 : ∀ e : ℕ, 2 ^ (2 * e + 1) % 3 = 2 := by
          intro e
          induction e with
          | zero => rfl
          | succ e ih =>
            have : 2 ^ (2 * (e + 1) + 1) = 4 * 2 ^ (2 * e + 1) := by ring
            omega
        have h3d : 3 ^ b % 3 = 0 := by
          have : (3 : ℕ) ∣ 3 ^ b := dvd_pow_self 3 hb.ne'
          omega
        have hx : (3 ^ b + 1) % 3 = 2 := by rw [← h]; exact h4 e
        omega
    obtain ⟨f, hf⟩ := haeven
    subst hf
    -- `(2^f - 1)(2^f + 1) = 3^b`, both factors are powers of three differing by two.
    have hfpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    obtain ⟨y, hy⟩ : ∃ y, 2 ^ f = y + 1 := ⟨2 ^ f - 1, by omega⟩
    have e2 : y * (y + 2) + 1 = 3 ^ b + 1 := by
      calc y * (y + 2) + 1 = (y + 1) * (y + 1) := by ring
        _ = 3 ^ b + 1 := by rw [← hy, ← pow_add]; exact h
    have hfact : (2 ^ f - 1) * (2 ^ f + 1) = 3 ^ b := by
      rw [hy]
      calc (y + 1 - 1) * (y + 1 + 1) = y * (y + 2) := by congr 1 <;> omega
        _ = 3 ^ b := by omega
    have hd1 : (2 ^ f - 1) ∣ 3 ^ b := ⟨2 ^ f + 1, hfact.symm⟩
    have hd2 : (2 ^ f + 1) ∣ 3 ^ b := ⟨2 ^ f - 1, by rw [← hfact]; ring⟩
    obtain ⟨i, hi, hei⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd1
    obtain ⟨j, hj, hej⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd2
    have hij : 3 ^ i + 2 = 3 ^ j := by omega
    obtain ⟨hi0, hj1⟩ := pow_three_add_two hij
    subst hi0
    rw [pow_zero] at hei
    have hf1 : f = 1 := by
      have h2f : 2 ^ f = 2 := by omega
      rcases Nat.lt_or_ge f 2 with hf2 | hf2
      · interval_cases f <;> omega
      · exfalso
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by omega) hf2
        omega
    subst hf1
    refine ⟨rfl, ?_⟩
    have h3b : 3 ^ b = 3 := by omega
    rcases Nat.lt_or_ge b 2 with hb2 | hb2
    · interval_cases b <;> omega
    · exfalso
      have : 3 ^ 2 ≤ 3 ^ b := Nat.pow_le_pow_right (by omega) hb2
      omega

/-- `3^d = 2^a + 1` forces `(a, d) = (1, 1)` or `(3, 2)`. -/
theorem pow_three_eq_pow_two_add_one {a d : ℕ} (h : 3 ^ d = 2 ^ a + 1) :
    (a = 1 ∧ d = 1) ∨ (a = 3 ∧ d = 2) := by
  rcases Nat.lt_or_ge a 3 with ha | ha
  · left
    have hpos : 0 < 3 ^ d := by positivity
    interval_cases a
    · exfalso
      rcases Nat.lt_or_ge d 1 with hd | hd
      · interval_cases d <;> omega
      · have : 3 ^ 1 ≤ 3 ^ d := Nat.pow_le_pow_right (by omega) hd
        omega
    · refine ⟨rfl, ?_⟩
      rcases Nat.lt_or_ge d 2 with hd | hd
      · interval_cases d <;> omega
      · exfalso
        have : 3 ^ 2 ≤ 3 ^ d := Nat.pow_le_pow_right (by omega) hd
        omega
    · exfalso
      rcases Nat.lt_or_ge d 2 with hd | hd
      · interval_cases d <;> omega
      · have : 3 ^ 2 ≤ 3 ^ d := Nat.pow_le_pow_right (by omega) hd
        omega
  · right
    have h8 : (8 : ℕ) ∣ 2 ^ a := by
      have : (2 : ℕ) ^ 3 ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
      simpa using this
    have hdeven : Even d := by
      rcases Nat.even_or_odd d with he | ho
      · exact he
      · exfalso
        obtain ⟨e, he⟩ := ho
        subst he
        have h9 : ∀ e : ℕ, 3 ^ (2 * e + 1) % 8 = 3 := by
          intro e
          induction e with
          | zero => rfl
          | succ e ih =>
            have : 3 ^ (2 * (e + 1) + 1) = 9 * 3 ^ (2 * e + 1) := by ring
            omega
        have hx : (2 ^ a + 1) % 8 = 3 := by rw [← h]; exact h9 e
        have h8' : 2 ^ a % 8 = 0 := by omega
        omega
    obtain ⟨e, he⟩ := hdeven
    subst he
    have hepos : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by omega)
    obtain ⟨y, hy⟩ : ∃ y, 3 ^ e = y + 1 := ⟨3 ^ e - 1, by omega⟩
    have e2 : y * (y + 2) + 1 = 2 ^ a + 1 := by
      calc y * (y + 2) + 1 = (y + 1) * (y + 1) := by ring
        _ = 2 ^ a + 1 := by rw [← hy, ← pow_add]; exact h
    have hfact : (3 ^ e - 1) * (3 ^ e + 1) = 2 ^ a := by
      rw [hy]
      calc (y + 1 - 1) * (y + 1 + 1) = y * (y + 2) := by congr 1 <;> omega
        _ = 2 ^ a := by omega
    have hd1 : (3 ^ e - 1) ∣ 2 ^ a := ⟨3 ^ e + 1, hfact.symm⟩
    have hd2 : (3 ^ e + 1) ∣ 2 ^ a := ⟨3 ^ e - 1, by rw [← hfact]; ring⟩
    obtain ⟨i, hi, hei⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    obtain ⟨j, hj, hej⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hij : 2 ^ i + 2 = 2 ^ j := by omega
    obtain ⟨hi1, hj2⟩ := pow_two_add_two hij
    subst hi1
    have h3e : 3 ^ e = 3 := by
      rw [pow_one] at hei
      omega
    have he1 : e = 1 := by
      rcases Nat.lt_or_ge e 2 with he2 | he2
      · interval_cases e <;> omega
      · exfalso
        have : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by omega) he2
        omega
    subst he1
    refine ⟨?_, rfl⟩
    have h2a : 2 ^ a = 8 := by omega
    rcases Nat.lt_or_ge a 4 with ha4 | ha4
    · interval_cases a <;> omega
    · exfalso
      have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha4
      omega

/-- **Consecutive three-smooth pairs** (Catalan-free): if `u ≥ 1` and both `u` and `u + 1`
are `3`-smooth, then `u ∈ {1, 2, 3, 8}`: the consecutive pairs in the two–three semigroup
are exactly `(1,2), (2,3), (3,4), (8,9)`. -/
theorem consecutive_threeSmooth_pairs {u : ℕ} (hu : 1 ≤ u)
    (h0 : IsThreeSmooth u) (h1 : IsThreeSmooth (u + 1)) :
    u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 8 := by
  rcases Nat.mod_two_eq_zero_or_one u with he | ho
  · -- `u` even, `u + 1 = 3^d` odd
    obtain ⟨d, hd⟩ := odd_threeSmooth h1 (by omega)
    have hd1 : d ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hd
      omega
    have h3u1 : 3 ∣ u + 1 := by rw [hd]; exact dvd_pow_self 3 hd1
    obtain ⟨a, b, hab⟩ := h0
    have hb0 : b = 0 := by
      by_contra hb
      have : 3 ∣ u := by rw [hab]; exact Dvd.dvd.mul_left (dvd_pow_self 3 hb) _
      omega
    subst hb0
    rw [pow_zero, mul_one] at hab
    subst hab
    have := pow_three_eq_pow_two_add_one (a := a) (d := d) (by omega)
    rcases this with ⟨ha, -⟩ | ⟨ha, -⟩ <;> subst ha <;> omega
  · -- `u = 3^b` odd, `u + 1` a power of two
    obtain ⟨b, hb⟩ := odd_threeSmooth h0 (by omega)
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · left
      rw [pow_zero] at hb
      omega
    · have h3u : 3 ∣ u := by rw [hb]; exact dvd_pow_self 3 hbpos.ne'
      obtain ⟨c, d2, hcd⟩ := h1
      have hd0 : d2 = 0 := by
        by_contra hd
        have : 3 ∣ u + 1 := by rw [hcd]; exact Dvd.dvd.mul_left (dvd_pow_self 3 hd) _
        omega
      subst hd0
      rw [pow_zero, mul_one] at hcd
      have := pow_two_eq_pow_three_add_one (a := c) (b := b) (by omega)
      rcases this with ⟨-, hb0⟩ | ⟨-, hb1⟩
      · exact absurd hb0 hbpos.ne'
      · subst hb1
        rw [pow_one] at hb
        omega

end LeanProofs.TwoBaseIntegerExponent.SmoothSemigroup
