import Diophantine.Paper1982.ShortPackingBounds
import Diophantine.Paper1982.ShortBase
import Diophantine.Paper1982.Packing

/-!
# The packed carry test in Jones 1982, §5

The three blocks have lengths `Q`, `2zQ²`, and `8Q²`. Their product is
`16zQ⁵`. The bounds are proved from the coding equations before imposing
any carry test, so packing does not add hidden size assumptions.
-/

namespace Jones1982

/-- The total block length (D17). -/
def shortPackedN (z Q : ℕ) : ℕ := Q * (2 * z * Q ^ 2) * (8 * Q ^ 2)

theorem shortPackedN_eq (z Q : ℕ) : shortPackedN z Q = 16 * z * Q ^ 5 := by
  unfold shortPackedN
  ring

/-- The left operand of (D16). -/
def shortPackedS (z B c e g l Q lam : ℕ) : ℕ :=
  pack3 Q (2 * z * Q ^ 2) g (l + e * Q) (shortS3 z B c e Q lam).toNat

/-- The right operand of (D16), with all three masks interpreted over `ℤ`. -/
def shortPackedT (z b B l Q lam : ℕ) : ℕ :=
  pack3 Q (2 * z * Q ^ 2) ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat
    (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat (((B : ℤ) - 2) * Q).toNat

/-- The mixed blocks preserve the carry test and yield one central-binomial
divisibility condition, as in (D16)–(D18). -/
theorem short_packing_iff {z b B c e g l Q lam s k : ℕ}
    (hz : z = 2 ^ s) (hQ : Q = 2 ^ k)
    (hbounds : ShortPackingBounds z b B c e g l Q lam) :
    (τ 2 g ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat = 0 ∧
      τ 2 (l + e * Q) (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat = 0 ∧
      τ 2 (shortS3 z B c e Q lam).toNat (((B : ℤ) - 2) * Q).toNat = 0) ↔
    (shortPackedN z Q) ^ 2 ∣
      (2 * centralCode (shortPackedN z Q) (shortPackedS z B c e g l Q lam)
        (shortPackedT z b B l Q lam)).choose
          (centralCode (shortPackedN z Q) (shortPackedS z B c e g l Q lam)
            (shortPackedT z b B l Q lam)) := by
  obtain ⟨hS1, hT10, hT1, hS2, hT20, hT2, hS30, hS3, hT30, hT3⟩ := hbounds
  have hT1n : ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat < Q := by
    rw [Int.toNat_lt hT10]
    exact hT1
  have hT2n : (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat < 2 * z * Q ^ 2 := by
    rw [Int.toNat_lt hT20]
    exact_mod_cast hT2
  have hS3n : (shortS3 z B c e Q lam).toNat < 8 * Q ^ 2 := by
    rw [Int.toNat_lt hS30.le]
    exact_mod_cast hS3
  have hT3n : (((B : ℤ) - 2) * Q).toNat < 8 * Q ^ 2 := by
    rw [Int.toNat_lt hT30]
    exact_mod_cast hT3
  have hN2 : 2 * z * Q ^ 2 = 2 ^ (1 + s + k * 2) := by
    rw [hz, hQ, pow_add, pow_add, pow_one, pow_mul]
  have hN : shortPackedN z Q = 2 ^ (4 + s + k * 5) := by
    rw [shortPackedN_eq, hz, hQ, pow_add, pow_add, pow_mul]
    norm_num
  have hS : shortPackedS z B c e g l Q lam < shortPackedN z Q :=
    pack3_lt hS1 hS2 hS3n
  have hT : shortPackedT z b B l Q lam < shortPackedN z Q :=
    pack3_lt hT1n hT2n hT3n
  have hτ := lemma_2_11_three (by rwa [← hQ] : g < 2 ^ k)
    (by rwa [← hQ] : ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat < 2 ^ k)
    (by rwa [← hN2] : l + e * Q < 2 ^ (1 + s + k * 2))
    (by rwa [← hN2] : (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat < 2 ^ (1 + s + k * 2))
    (S₃ := (shortS3 z B c e Q lam).toNat) (T₃ := (((B : ℤ) - 2) * Q).toNat)
  rw [← hQ, ← hN2] at hτ
  change _ ↔ τ 2 (shortPackedS z B c e g l Q lam) (shortPackedT z b B l Q lam) = 0 at hτ
  refine hτ.trans ?_
  have hdvd := lemma_2_16 (by rwa [← hN] : shortPackedS z B c e g l Q lam < 2 ^ (4 + s + k * 5))
    (by rwa [← hN] : shortPackedT z b B l Q lam < 2 ^ (4 + s + k * 5))
    (R := centralCode (shortPackedN z Q) (shortPackedS z B c e g l Q lam)
      (shortPackedT z b B l Q lam)) (by rw [← hN]; rfl)
  rwa [← hN] at hdvd

/-- The size chain for Lemma 2.26, without assuming the power equation
that this lemma will subsequently recover. -/
theorem short_packing_sizes {ν z b B Q lam N R S T : ℕ}
    (hz : 2 ≤ z) (hb2 : 2 ≤ b) (hbase : B = shortBase ν z b)
    (hlam : 0 < lam) (hgeom : Q = 1 + lam * (B - 1))
    (hN : N = shortPackedN z Q) (hR : R = centralCode N S T) :
    3 < 3 * L4 ν ∧ 3 * L4 ν ≤ B ∧ B ≤ Q ∧ Q ≤ N ∧ N ≤ R ∧
      8 ≤ N ∧ 8 ≤ R ∧ b ≤ N ∧ b ≤ R := by
  obtain ⟨hbB, hzB, hLB⟩ := shortBase_bounds (ν := ν) hz (by omega : 1 ≤ b)
  rw [← hbase] at hbB hzB hLB
  have hBQ : B ≤ Q := by
    have := Nat.le_mul_of_pos_left (B - 1) hlam
    omega
  have hQ0 : 0 < Q := by omega
  have hQN : Q ≤ N := by
    rw [hN, shortPackedN]
    exact (Nat.le_mul_of_pos_right Q (by positivity)).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  have hNR : N ≤ R := by rw [hR]; exact centralCode_ge_base (by omega)
  have hL : 5 ≤ L4 ν := by
    change 5 ≤ 5 ^ (ν + 1)
    exact Nat.le_self_pow (by omega) 5
  omega

/-- The same size chain specialized to the retained-power coding system. -/
theorem ShortEqs.packing_sizes {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {x z u y b B c e g l m Q t lam ε N R : ℕ} (hI : Index ν P z u y)
    (hx : 0 < x) (hε : 0 < ε) (h : ShortEqs ν x z u y b B c e g l m Q t lam ε)
    (hN : N = shortPackedN z Q)
    (hR : R = centralCode N (shortPackedS z B c e g l Q lam) (shortPackedT z b B l Q lam)) :
    3 < 3 * L4 ν ∧ 3 * L4 ν ≤ B ∧ B ≤ Q ∧ Q ≤ N ∧ N ≤ R ∧
      8 ≤ N ∧ 8 ≤ R ∧ b ≤ N ∧ b ≤ R := by
  have hb2 : 2 ≤ b := by have := h.D1; omega
  have hB2 : 2 ≤ B := by
    have hbase := shortBase_bounds (ν := ν) hI.two_le (by omega : 1 ≤ b)
    rw [← h.D2] at hbase
    omega
  exact short_packing_sizes hI.two_le hb2 h.D2 (h.lam_pos hB2) h.D7 hN hR

end Jones1982
