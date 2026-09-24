import Diophantine.Paper1982.PowerExtension
import Diophantine.Paper1982.Psi
import Diophantine.Paper1982.PellPowerQuotient
import Diophantine.Paper1982.PellQuotient

/-!
# The polynomial Pell subsystem in Jones 1982, §5

These are (D3)–(D5) and (D19)–(D37), with `L = 5^(ν+1)` supplied as
a parameter. No power equation, binomial coefficient, or Pell sequence
is included in the conditions. Every witness is strictly positive.
Subtractions in the displayed polynomial equations are interpreted in `ℤ`.
The strict rational inequality (D21) is cleared using the positive `K`.
The equation for `G` uses the printed alternate `F²−A` formula.
-/

namespace Jones1982

/-- The twenty-seven positive witnesses of the §5 Pell subsystem.
The field `w` is the multiplier in `W=bw`, not the eliminated exponent of `b`. -/
structure ShortPellWitnesses (R N b B L Q : ℕ) where
  A : ℕ
  C : ℕ
  C₁ : ℕ
  D : ℕ
  D₁ : ℕ
  E : ℕ
  F : ℕ
  G : ℕ
  H : ℕ
  I : ℕ
  K : ℕ
  M : ℕ
  P : ℕ
  U : ℕ
  V : ℕ
  W : ℕ
  Y : ℕ
  h : ℕ
  i : ℕ
  j : ℕ
  o : ℕ
  s : ℕ
  w : ℕ
  α : ℕ
  Δ : ℕ
  γ : ℕ
  φ : ℕ
  A_pos : 0 < A
  C_pos : 0 < C
  C₁_pos : 0 < C₁
  D_pos : 0 < D
  D₁_pos : 0 < D₁
  E_pos : 0 < E
  F_pos : 0 < F
  G_pos : 0 < G
  H_pos : 0 < H
  I_pos : 0 < I
  K_pos : 0 < K
  M_pos : 0 < M
  P_pos : 0 < P
  U_pos : 0 < U
  V_pos : 0 < V
  W_pos : 0 < W
  Y_pos : 0 < Y
  h_pos : 0 < h
  i_pos : 0 < i
  j_pos : 0 < j
  o_pos : 0 < o
  s_pos : 0 < s
  w_pos : 0 < w
  α_pos : 0 < α
  Δ_pos : 0 < Δ
  γ_pos : 0 < γ
  φ_pos : 0 < φ
  D3 : (D₁ : ℤ) = Q + C₁ * ((A : ℤ) - B) + α * (2 * (A : ℤ) * B - B ^ 2 - 1)
  D4 : ((A : ℤ) ^ 2 - 1) * C₁ ^ 2 + 1 = (D₁ : ℤ) ^ 2
  D5 : (C₁ : ℤ) = L + Δ * ((A : ℤ) - 1)
  D19 : P = 2 * M ^ 2 * U
  D20 : IsSquare (((P : ℤ) ^ 2 - 1) * K ^ 2 + 1)
  D21 : 4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2
  D22 : (K : ℤ) = R + 1 + h * ((P : ℤ) - 1)
  D23 : M = R * Y
  D24 : A = M * (U + 1)
  D25 : C = 2 * R + 1 + C₁ + φ
  D26 : U = N ^ 2 * w
  D27 : Y = N ^ 2 * s
  D28 : W = b * w
  D29 : V = 2
  D30 : (D : ℤ) = W + C * ((A : ℤ) - V) + γ * (2 * (A : ℤ) * V - V ^ 2 - 1)
  D31 : I = D + o * F
  D32 : (D : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * C ^ 2 + 1
  D33 : E = i * C ^ 2
  D34 : (F : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * E ^ 2 + 1
  D35 : (G : ℤ) = A + F ^ 2 * ((F : ℤ) ^ 2 - A)
  D36 : H = 2 * R + 1 + j * C
  D37 : (I : ℤ) ^ 2 = ((G : ℤ) ^ 2 - 1) * H ^ 2 + 1

end Jones1982
