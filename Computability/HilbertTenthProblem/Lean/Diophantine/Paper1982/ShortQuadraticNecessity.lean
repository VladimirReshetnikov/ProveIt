import Diophantine.Paper1982.ShortQuadraticBridgeDefs
import Diophantine.Paper1982.ShortPolynomialDefs

/-!
# Positive witnesses for the explicit quadratic system

The full system (D1)–(D37) supplies the thirty-six retained variables and
the nineteen product auxiliaries. Strict inequalities supply positive
integer slacks, and the square in (D20) supplies a positive natural root.
Thus the substitutions and degree reduction preserve positive solvability.
-/

namespace Jones1982.ShortPolynomialWitnesses

open ShortQuadratic ShortQuadraticExpr

set_option maxHeartbeats 2000000 in
/-- Every positive solution of the original fifty-three-witness system
gives a positive solution of the forty-six quadratic equations. -/
theorem exists_positiveWitnesses {ν x z u y : ℕ}
    (hz : 2 ≤ z) (hx : 0 < x) (h : ShortPolynomialWitnesses ν x z u y) :
    Nonempty (PositiveWitnesses x z u y (L4 ν)) := by
  let hp := h.pell
  have hb := h.b_pos
  have hB := h.B_pos
  have hc := h.c_pos
  have he := h.e_pos
  have hg := h.g_pos
  have hl := h.l_pos
  have hm := h.m_pos
  have hQ := h.Q_pos
  have ht := h.t_pos
  have hlam := h.lam_pos
  have hε := h.ε_pos
  have hN := h.N_pos
  have hR := h.R_pos
  have hS := h.S_pos
  have hT := h.T_pos
  have hA := hp.A_pos
  have hC := hp.C_pos
  have hC₁ := hp.C₁_pos
  have hD := hp.D_pos
  have hD₁ := hp.D₁_pos
  have hE := hp.E_pos
  have hF := hp.F_pos
  have hG := hp.G_pos
  have hH := hp.H_pos
  have hI := hp.I_pos
  have hK := hp.K_pos
  have hM := hp.M_pos
  have hP := hp.P_pos
  have hU := hp.U_pos
  have hY := hp.Y_pos
  have hh := hp.h_pos
  have hi := hp.i_pos
  have hj := hp.j_pos
  have ho := hp.o_pos
  have hs := hp.s_pos
  have hw := hp.w_pos
  have hα := hp.α_pos
  have hΔ := hp.Δ_pos
  have hγ := hp.γ_pos
  have hφ := hp.φ_pos
  have hBR : h.B ≤ h.R := by
    obtain ⟨_, _, hBQ, hQN, hNR, _⟩ := h.sizes hz hx
    exact hBQ.trans (hQN.trans hNR)
  have hRM : h.R ≤ hp.M := by
    rw [hp.D23]
    exact Nat.le_mul_of_pos_right h.R hY
  have hMA : hp.M < hp.A := by
    rw [hp.D24]
    exact lt_mul_of_one_lt_right hM (by omega)
  have hBA : h.B < hp.A := lt_of_le_of_lt (hBR.trans hRM) hMA
  let J : ℤ := 2 * (hp.A : ℤ) * h.B - h.B ^ 2 - 1
  have hJ : 0 < J := by
    have hbound := lemma_2_21 hB hBA
    have hboundZ : (hp.A : ℤ) + (h.B : ℤ) ^ 2 + 1 ≤ 2 * hp.A * h.B := by
      exact_mod_cast (show hp.A + h.B ^ 2 + 1 ≤ 2 * hp.A * h.B by
        simpa only [pow_two] using hbound)
    have hAZ : (0 : ℤ) < hp.A := by exact_mod_cast hA
    dsimp [J]
    omega
  have hJcast : (J.toNat : ℤ) = J := Int.toNat_of_nonneg hJ.le
  have hJnat : 0 < J.toNat := by
    exact_mod_cast (show (0 : ℤ) < J.toNat by omega)
  let ξ : ℕ :=
    ((2 : ℤ) * z * h.Q - (h.e + 2 * (z : ℤ) * h.b * h.l +
      2 * (z : ℤ) * h.B * h.c ^ 4)).toNat
  have hD8Z : (h.e : ℤ) + 2 * z * h.b * h.l + 2 * z * h.B * h.c ^ 4 <
      2 * z * h.Q := by exact_mod_cast h.D8
  have hξeq : (ξ : ℤ) = 2 * (z : ℤ) * h.Q -
      (h.e + 2 * (z : ℤ) * h.b * h.l + 2 * (z : ℤ) * h.B * h.c ^ 4) :=
    Int.toNat_of_nonneg (by omega)
  have hξ : 0 < ξ := by
    exact_mod_cast (show (0 : ℤ) < ξ by omega)
  let η : ℕ :=
    ((hp.K : ℤ) ^ 2 - 4 * ((hp.C : ℤ) - hp.K * hp.Y) ^ 2).toNat
  have hηeq : (η : ℤ) =
      (hp.K : ℤ) ^ 2 - 4 * ((hp.C : ℤ) - hp.K * hp.Y) ^ 2 :=
    Int.toNat_of_nonneg (by have := hp.D21; omega)
  have hη : 0 < η := by
    have := hp.D21
    exact_mod_cast (show (0 : ℤ) < η by omega)
  obtain ⟨root, hroot⟩ := hp.D20
  let τ : ℕ := root.natAbs
  have hτeq : ((hp.P : ℤ) ^ 2 - 1) * hp.K ^ 2 + 1 = (τ : ℤ) ^ 2 := by
    change ((hp.P : ℤ) ^ 2 - 1) * hp.K ^ 2 + 1 = (root.natAbs : ℤ) ^ 2
    rw [Int.natCast_natAbs, sq_abs]
    simpa only [pow_two] using hroot
  have hτ : 0 < τ := by
    have hP2 : (1 : ℤ) ≤ (hp.P : ℤ) ^ 2 := by
      exact_mod_cast (Nat.one_le_pow 2 hp.P hP)
    have hnonneg : 0 ≤ ((hp.P : ℤ) ^ 2 - 1) * hp.K ^ 2 :=
      mul_nonneg (by omega) (sq_nonneg _)
    by_contra hnot
    have hzero : τ = 0 := by omega
    rw [hzero] at hτeq
    norm_num at hτeq
    linarith only [hτeq, hnonneg]
  let v : ShortQuadraticVar → ℕ
    | .B => h.B
    | .C₁ => hp.C₁
    | .D => hp.D
    | .D₁ => hp.D₁
    | .E => hp.E
    | .F => hp.F
    | .G => hp.G
    | .H => hp.H
    | .I => hp.I
    | .K => hp.K
    | .M => hp.M
    | .N => h.N
    | .P => hp.P
    | .R => h.R
    | .S => h.S
    | .T => h.T
    | .U => hp.U
    | .Y => hp.Y
    | .c => h.c
    | .e => h.e
    | .g => h.g
    | .h => hp.h
    | .i => hp.i
    | .j => hp.j
    | .l => h.l
    | .m => h.m
    | .o => hp.o
    | .s => hp.s
    | .t => h.t
    | .w => hp.w
    | .alpha => hp.α
    | .delta => hp.Δ
    | .gamma => hp.γ
    | .lam => h.lam
    | .phi => hp.φ
    | .epsilon => h.ε
    | .lamB => h.lam * h.B
    | .bSq => h.b ^ 2
    | .pellMod => J.toNat
    | .AC₁ => hp.A * hp.C₁
    | .cSq => h.c ^ 2
    | .cFourth => h.c ^ 4
    | .xi => ξ
    | .QSq => h.Q ^ 2
    | .QCube => h.Q ^ 3
    | .QFourth => h.Q ^ 4
    | .cFourthQCube => h.c ^ 4 * h.Q ^ 3
    | .NSq => h.N ^ 2
    | .MU => hp.M * hp.U
    | .PK => hp.P * hp.K
    | .tau => τ
    | .YK => hp.Y * hp.K
    | .eta => η
    | .AC => hp.A * hp.C
    | .CSq => hp.C ^ 2
    | .AE => hp.A * hp.E
    | .FSq => hp.F ^ 2
    | .GH => hp.G * hp.H
  refine ⟨⟨v, ?_, ?_⟩⟩
  · intro idx
    cases idx <;> dsimp only [v] <;> positivity
  have hbZ : (h.ε : ℤ) + x = h.b := by exact_mod_cast h.D1.symm
  have hAZ : (hp.M : ℤ) * hp.U + hp.M = hp.A := by
    have heq : (hp.A : ℤ) = hp.M * (hp.U + 1) := by exact_mod_cast hp.D24
    linear_combination -heq
  have hCZ : 2 * (h.R : ℤ) + 1 + hp.C₁ + hp.φ = hp.C := by
    exact_mod_cast hp.D25.symm
  have hQZ : (1 : ℤ) + h.lam * h.B - h.lam = h.Q := by
    linear_combination -h.D7
  have hD2Z : (h.B : ℤ) =
      2 * (h.b : ℤ) ^ 4 * (2 * (z : ℤ)) ^ (L4 ν + 1) := by
    exact_mod_cast h.D2
  have hD6Z : (h.c : ℤ) = 1 + x * h.B + h.g := by exact_mod_cast h.D6
  have hSZ : (h.S : ℤ) = h.g + h.l * (h.Q : ℤ) + h.e * (h.Q : ℤ) ^ 2 -
      4 * (z : ℤ) * ((h.c : ℤ) ^ 4 * (h.Q : ℤ) ^ 3) *
        ((z : ℤ) * (h.lam + (h.Q : ℤ)) - h.e) +
      2 * (z : ℤ) * (h.lam * (h.B : ℤ)) * ((h.Q : ℤ) ^ 3 + (h.Q : ℤ) ^ 4) := by
    have heq := congrArg (fun n : ℕ => (n : ℤ)) h.D16.1
    rw [h.D13.1, h.D14.1, h.D13.2.2, h.D14.2.2] at heq
    push_cast at heq
    rw [h.D15.1, h.D12] at heq
    linear_combination heq
  have hTZ : (h.T : ℤ) = h.Q - 1 - ((h.b : ℤ) - 1) * h.l +
      (h.lam * (h.B : ℤ) - 2 * (z : ℤ) * h.lam) * (h.Q + (h.Q : ℤ) ^ 2) +
      2 * (z : ℤ) * ((h.B : ℤ) - 2) * (h.Q : ℤ) ^ 4 := by
    have heq := congrArg (fun n : ℕ => (n : ℤ)) h.D16.2
    rw [h.D13.2.1, h.D13.2.2, h.D14.2.2] at heq
    push_cast at heq
    rw [h.D11, h.D14.2.1, h.D15.2.1] at heq
    linear_combination heq
  have hNZ : (h.N : ℤ) = 16 * (z : ℤ) * h.Q * (h.Q : ℤ) ^ 4 := by
    have heq := congrArg (fun n : ℕ => (n : ℤ)) h.D17
    rw [h.D13.2.2, h.D14.2.2, h.D15.2.2] at heq
    push_cast at heq
    linear_combination heq
  have hD19Z : (hp.P : ℤ) = 2 * (hp.M : ℤ) ^ 2 * hp.U := by
    exact_mod_cast hp.D19
  have hD23Z : (hp.M : ℤ) = h.R * (hp.Y : ℤ) := by exact_mod_cast hp.D23
  have hD26Z : (hp.U : ℤ) = (h.N : ℤ) ^ 2 * hp.w := by exact_mod_cast hp.D26
  have hD27Z : (hp.Y : ℤ) = (h.N : ℤ) ^ 2 * hp.s := by exact_mod_cast hp.D27
  have hD30Z : (hp.D : ℤ) = h.b * (hp.w : ℤ) + hp.C * ((hp.A : ℤ) - 2) +
      hp.γ * (4 * (hp.A : ℤ) - 5) := by
    have heq := hp.D30
    rw [hp.D28, hp.D29] at heq
    push_cast at heq
    linear_combination heq
  have hD31Z : (hp.I : ℤ) = hp.D + hp.o * (hp.F : ℤ) := by
    exact_mod_cast hp.D31
  have hD33Z : (hp.E : ℤ) = hp.i * (hp.C : ℤ) ^ 2 := by
    exact_mod_cast hp.D33
  have hD36Z : (hp.H : ℤ) = 2 * (h.R : ℤ) + 1 + hp.j * (hp.C : ℤ) := by
    exact_mod_cast hp.D36
  intro idx
  cases idx <;>
    simp only [ShortQuadratic.residual, expression, bExpr, AExpr, CExpr, QExpr,
      toPolynomial_sub, toPolynomial_pow, ShortQuadraticExpr.toPolynomial,
      MvPolynomial.eval_add, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
      MvPolynomial.eval_X, assignment, v, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, hbZ, hAZ, hJcast, hξeq, hηeq, J] <;>
    try simp only [hCZ, hQZ]
  case lamB => ring
  case bSq => ring
  case pellMod => ring
  case AC₁ => ring
  case cSq => ring
  case cFourth => ring
  case QSq => ring
  case QCube => ring
  case QFourth => ring
  case cFourthQCube => ring
  case NSq => ring
  case MU => ring
  case PK => ring
  case YK => ring
  case AC => ring
  case CSq => ring
  case AE => ring
  case FSq => ring
  case GH => ring
  case D2 => linear_combination hD2Z
  case D3 => linear_combination hp.D3
  case D4 => linear_combination hp.D4
  case D5 =>
    have heq := hp.D5
    simp only [L4_eq, Nat.cast_pow, Nat.cast_ofNat] at heq ⊢
    linear_combination heq
  case D6 => linear_combination hD6Z
  case D8 => ring
  case D9 => linear_combination h.D9
  case D10 => linear_combination h.D10
  case D16S => linear_combination hSZ
  case D16T => linear_combination hTZ
  case D17 => linear_combination hNZ
  case D18 => linear_combination h.D18
  case D19 => linear_combination hD19Z
  case D20 => linear_combination hτeq
  case D21 => ring
  case D22 => linear_combination hp.D22
  case D23 => linear_combination hD23Z
  case D26 => linear_combination hD26Z
  case D27 => linear_combination hD27Z
  case D30 => linear_combination hD30Z
  case D31 => linear_combination hD31Z
  case D32 => linear_combination hp.D32
  case D33 => linear_combination hD33Z
  case D34 => linear_combination hp.D34
  case D35 => linear_combination hp.D35
  case D36 => linear_combination hD36Z
  case D37 => linear_combination hp.D37

end Jones1982.ShortPolynomialWitnesses
