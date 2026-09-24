import Diophantine.Paper1982.ShortPellDefs
import Diophantine.Paper1982.ShortPackedMaster

/-!
# The complete system (D1)–(D37) in Jones 1982, §5

There are twenty-six scalar fields here and twenty-seven in `pell`, for
the article's fifty-three witnesses before substitution and degree reduction.
All witnesses except `D₀` are positive natural numbers; `D₀` is an integer.
The equations use integer subtraction. The only large exponent occurs in
the coefficient `2(2z)^(L+1)` of (D2), with `z` and `L` fixed parameters.
The predicates for a square and a strict inequality are retained as printed.
-/

namespace Jones1982

/-- The positive-witness version of (D1)–(D37), before degree reduction.
There is no retained power equation or central-binomial test. -/
structure ShortPolynomialWitnesses (ν x z u y : ℕ) where
  b : ℕ
  B : ℕ
  c : ℕ
  e : ℕ
  g : ℕ
  l : ℕ
  m : ℕ
  Q : ℕ
  t : ℕ
  lam : ℕ
  ε : ℕ
  N : ℕ
  R : ℕ
  M₁ : ℕ
  D₀ : ℤ
  S₁ : ℕ
  S₂ : ℕ
  S₃ : ℕ
  T₁ : ℕ
  T₂ : ℕ
  T₃ : ℕ
  N₁ : ℕ
  N₂ : ℕ
  N₃ : ℕ
  S : ℕ
  T : ℕ
  pell : ShortPellWitnesses R N b B (L4 ν) Q
  b_pos : 0 < b
  B_pos : 0 < B
  c_pos : 0 < c
  e_pos : 0 < e
  g_pos : 0 < g
  l_pos : 0 < l
  m_pos : 0 < m
  Q_pos : 0 < Q
  t_pos : 0 < t
  lam_pos : 0 < lam
  ε_pos : 0 < ε
  N_pos : 0 < N
  R_pos : 0 < R
  M₁_pos : 0 < M₁
  S₁_pos : 0 < S₁
  S₂_pos : 0 < S₂
  S₃_pos : 0 < S₃
  T₁_pos : 0 < T₁
  T₂_pos : 0 < T₂
  T₃_pos : 0 < T₃
  N₁_pos : 0 < N₁
  N₂_pos : 0 < N₂
  N₃_pos : 0 < N₃
  S_pos : 0 < S
  T_pos : 0 < T
  D1 : b = ε + x
  D2 : B = shortBase ν z b
  D6 : c = 1 + x * B + g
  D7 : (Q : ℤ) = 1 + lam * ((B : ℤ) - 1)
  D8 : e + 2 * z * b * l + 2 * z * B * c ^ 4 < 2 * z * Q
  D9 : (l : ℤ) = u + t * ((B : ℤ) - 2 * z)
  D10 : (e : ℤ) = y + m * ((B : ℤ) - 2 * z)
  D11 : (M₁ : ℤ) = Q - 1 - ((b : ℤ) - 1) * l
  D12 : D₀ = z * ((lam : ℤ) + Q) - e
  D13 : S₁ = g ∧ T₁ = M₁ ∧ N₁ = Q
  D14 : S₂ = l + e * Q ∧ (T₂ : ℤ) = ((B : ℤ) - 2 * z) * lam * (1 + Q) ∧
    N₂ = 2 * z * Q ^ 2
  D15 : (S₃ : ℤ) = -2 * (c : ℤ) ^ 4 * D₀ + B * lam * (1 + Q) ∧
    (T₃ : ℤ) = ((B : ℤ) - 2) * Q ∧ N₃ = 8 * Q ^ 2
  D16 : S = S₁ + S₂ * N₁ + S₃ * N₁ * N₂ ∧
    T = T₁ + T₂ * N₁ + T₃ * N₁ * N₂
  D17 : N = N₁ * N₂ * N₃
  D18 : (R : ℤ) = S * ((N : ℤ) ^ 2 - N) + (T + 1) * ((N : ℤ) ^ 2 - 1)

/-- The geometric relation has its intended natural-number reading. -/
theorem ShortPolynomialWitnesses.geom_nat {ν x z u y : ℕ}
    (h : ShortPolynomialWitnesses ν x z u y) : h.Q = 1 + h.lam * (h.B - 1) := by
  zify [h.B_pos]
  exact h.D7

/-- The auxiliary block definitions agree with the previously proved packing
functions. No power equation or carry condition is used. -/
theorem ShortPolynomialWitnesses.packing_eqs {ν x z u y : ℕ}
    (h : ShortPolynomialWitnesses ν x z u y) :
    h.N = shortPackedN z h.Q ∧
    h.S = shortPackedS z h.B h.c h.e h.g h.l h.Q h.lam ∧
    h.T = shortPackedT z h.b h.B h.l h.Q h.lam ∧
    h.R = centralCode h.N h.S h.T := by
  have hM : h.M₁ = ((h.Q : ℤ) - 1 - ((h.b : ℤ) - 1) * h.l).toNat := by
    rw [← h.D11, Int.toNat_natCast]
  have hS3 : h.S₃ = (shortS3 z h.B h.c h.e h.Q h.lam).toNat := by
    have heq : (h.S₃ : ℤ) = shortS3 z h.B h.c h.e h.Q h.lam := by
      rw [h.D15.1, h.D12]
      rfl
    rw [← heq, Int.toNat_natCast]
  have hT2 : h.T₂ = (((h.B : ℤ) - 2 * z) * h.lam * (1 + h.Q)).toNat := by
    rw [← h.D14.2.1, Int.toNat_natCast]
  have hT3 : h.T₃ = (((h.B : ℤ) - 2) * h.Q).toNat := by
    rw [← h.D15.2.1, Int.toNat_natCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h.D17, h.D13.2.2, h.D14.2.2, h.D15.2.2]
    rfl
  · rw [h.D16.1, h.D13.1, h.D14.1, h.D13.2.2, h.D14.2.2, hS3]
    rfl
  · rw [h.D16.2, h.D13.2.1, h.D13.2.2, h.D14.2.2, hM, hT2, hT3]
    rfl
  · have hNsq : h.N ≤ h.N ^ 2 := Nat.le_self_pow (by norm_num) h.N
    have hN1 : 1 ≤ h.N ^ 2 := Nat.one_le_pow _ _ h.N_pos
    unfold centralCode
    zify [hNsq, hN1]
    exact h.D18

/-- The size prerequisites of Lemmas 2.25 and 2.26 follow before recovering
either power equation from the Pell subsystem. -/
theorem ShortPolynomialWitnesses.sizes {ν x z u y : ℕ}
    (h : ShortPolynomialWitnesses ν x z u y) (hz : 2 ≤ z) (hx : 0 < x) :
    3 < 3 * L4 ν ∧ 3 * L4 ν ≤ h.B ∧ h.B ≤ h.Q ∧ h.Q ≤ h.N ∧ h.N ≤ h.R ∧
      8 ≤ h.N ∧ 8 ≤ h.R ∧ h.b ≤ h.N ∧ h.b ≤ h.R := by
  have hb2 : 2 ≤ h.b := by have := h.D1; have := h.ε_pos; omega
  obtain ⟨hN, _, _, hR⟩ := h.packing_eqs
  exact short_packing_sizes hz hb2 h.D2 h.lam_pos h.geom_nat hN hR

end Jones1982
