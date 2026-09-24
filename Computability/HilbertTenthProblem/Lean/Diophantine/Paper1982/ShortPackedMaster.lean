import Diophantine.Paper1982.ShortMaster
import Diophantine.Paper1982.ShortPacking

/-!
# The packed shorter-system equivalence in Jones 1982, §5

The three carry conditions are replaced by one central-binomial
divisibility condition. The intended power equation remains explicit.
Every conversion from a signed mask to a natural mask is justified here.
-/

namespace Jones1982

/-- The shorter coding equations with one central-binomial divisibility test. -/
structure ShortPackedSys (ν : ℕ) (x z u y b B c e g l m Q t lam ε : ℕ) : Prop
    extends ShortEqs ν x z u y b B c e g l m Q t lam ε where
  dvd : (shortPackedN z Q) ^ 2 ∣
    (2 * centralCode (shortPackedN z Q) (shortPackedS z B c e g l Q lam)
      (shortPackedT z b B l Q lam)).choose
        (centralCode (shortPackedN z Q) (shortPackedS z B c e g l Q lam)
          (shortPackedT z b B l Q lam))

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The natural masks in `ShortSys` coincide with the signed masks used
for packing, so the two complete systems are equivalent. -/
theorem ShortEqs.shortSys_iff_packed (hI : Index ν P z u y)
    {x b B c e g l m Q t lam ε w : ℕ} (hx : 0 < x) (hε : 0 < ε) (hl : 0 < l)
    (hb : b = 2 ^ w) (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) :
    ShortSys ν x z u y b B c e g l m Q t lam ε ↔
      ShortPackedSys ν x z u y b B c e g l m Q t lam ε := by
  have hb2 : 2 ≤ b := by have := h.D1; omega
  obtain ⟨_, h4z, _⟩ := shortBase_bounds (ν := ν) hI.two_le (by omega : 1 ≤ b)
  rw [← h.D2] at h4z
  have h2zB : 2 * z ≤ B := by omega
  have hB2 : 2 ≤ B := by have := hI.two_le; omega
  have hT1 : ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat = Q - 1 - (b - 1) * l := by
    have hp : (((b - 1) * l : ℕ) : ℤ) = ((b : ℤ) - 1) * l := by
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
    rw [← hp]
    omega
  have hT2 : (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat =
      (B - 2 * z) * lam * (1 + Q) := by
    have hp : (((B - 2 * z) * lam * (1 + Q) : ℕ) : ℤ) =
        ((B : ℤ) - 2 * z) * lam * (1 + Q) := by
      simp only [Nat.cast_mul, Nat.cast_sub h2zB, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [← hp, Int.toNat_natCast]
  have hT3 : (((B : ℤ) - 2) * Q).toNat = (B - 2) * Q := by
    have hp : (((B - 2) * Q : ℕ) : ℤ) = ((B : ℤ) - 2) * Q := by
      simp only [Nat.cast_mul, Nat.cast_sub hB2, Nat.cast_ofNat]
    rw [← hp, Int.toNat_natCast]
  obtain ⟨s, hs⟩ := hI.pow2
  have hQpow : Q = 2 ^ ((1 + w * 4 + (s + 1) * (L4 ν + 1)) * L4 ν) := by
    rw [h.power, h.D2, shortBase_pow_two hs hb, ← pow_mul]
  have hi := short_packing_iff hs hQpow (h.packing_bounds hI hx hε hl)
  rw [hT1, hT2, hT3] at hi
  constructor
  · intro hS
    exact ⟨h, hi.1 ⟨hS.τ1, hS.τ2, hS.τ3⟩⟩
  · intro hS
    obtain ⟨h1, h2, h3⟩ := hi.2 hS.dvd
    exact ⟨h, h1, h2, h3⟩

/-- The full coding-stage equivalence after packing the three tests.
Elimination of the power equation and degree reduction remain separate. -/
theorem short_master_packed (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ b B c e g l m Q t lam ε w : ℕ,
      0 < b ∧ 0 < B ∧ 0 < c ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < Q ∧
      0 < t ∧ 0 < lam ∧ 0 < ε ∧ 0 < w ∧ b = 2 ^ w ∧
      ShortPackedSys ν x z u y b B c e g l m Q t lam ε := by
  rw [short_master hν hP hnorm hI hx]
  constructor <;>
    rintro ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
      hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, hpow, h⟩
  · exact ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
      hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, hpow,
      (h.toShortEqs.shortSys_iff_packed hI hx hε hl hpow).1 h⟩
  · exact ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
      hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, hpow,
      (h.toShortEqs.shortSys_iff_packed hI hx hε hl hpow).2 h⟩

end

end Jones1982
