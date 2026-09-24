import Diophantine.Paper1982.ShortQuadraticBridgeDefs
import Diophantine.Paper1982.ShortPolynomialDefs

/-!
# Reconstructing the full system from the fifty-eight quadratic witnesses

The auxiliary equations recover the eliminated quantities over the integers.
The geometric relation and the numeric packing bounds then establish the
positivity needed to interpret the eliminated blocks as natural numbers.
No power equation, carry condition, or Pell consequence is assumed here.
-/

namespace Jones1982.ShortQuadratic

set_option maxHeartbeats 2000000 in
/-- A positive solution of the explicit quadratic residuals reconstructs all
fifty-three witnesses of (D1)–(D37). -/
theorem PositiveWitnesses.exists_shortPolynomial {ν x z u y : ℕ}
    (hz : 2 ≤ z) (hx : 0 < x)
    (h : PositiveWitnesses x z u y (L4 ν)) :
    Nonempty (ShortPolynomialWitnesses ν x z u y) := by
  let v := h.val
  let b := v .epsilon + x
  let A := v .MU + v .M
  let C := 2 * v .R + 1 + v .C₁ + v .phi
  let Q := 1 + v .lam * (v .B - 1)
  have hp : ∀ idx, 0 < v idx := h.pos
  have hb : 2 ≤ b := by have := hp .epsilon; dsimp [b]; omega
  have hApos : 0 < A := by have := hp .M; dsimp [A]; omega
  have hCpos : 0 < C := by dsimp [C]; omega
  have hQpos : 0 < Q := by dsimp [Q]; omega
  have hBpos := hp .B
  have hlampos := hp .lam
  have hlpos := hp .l
  have heqs : ∀ idx : ShortQuadraticEquation,
      MvPolynomial.eval (assignment x v) (ShortQuadratic.residual z u y (L4 ν) idx) = 0 :=
    h.equations
  have hLamB := heqs .lamB
  have hBSq := heqs .bSq
  have hMod := heqs .pellMod
  have hAC₁ := heqs .AC₁
  have hCSmallSq := heqs .cSq
  have hCFourth := heqs .cFourth
  have hQSq := heqs .QSq
  have hQCube := heqs .QCube
  have hQFourth := heqs .QFourth
  have hCQ := heqs .cFourthQCube
  have hNSq := heqs .NSq
  have hMU := heqs .MU
  have hPK := heqs .PK
  have hYK := heqs .YK
  have hAC := heqs .AC
  have hCSq := heqs .CSq
  have hAE := heqs .AE
  have hFSq := heqs .FSq
  have hGH := heqs .GH
  have hD2 := heqs .D2
  have hD3 := heqs .D3
  have hD4 := heqs .D4
  have hD5 := heqs .D5
  have hD6 := heqs .D6
  have hD8 := heqs .D8
  have hD9 := heqs .D9
  have hD10 := heqs .D10
  have hD16S := heqs .D16S
  have hD16T := heqs .D16T
  have hD17 := heqs .D17
  have hD18 := heqs .D18
  have hD19 := heqs .D19
  have hD20 := heqs .D20
  have hD21 := heqs .D21
  have hD22 := heqs .D22
  have hD23 := heqs .D23
  have hD26 := heqs .D26
  have hD27 := heqs .D27
  have hD30 := heqs .D30
  have hD31 := heqs .D31
  have hD32 := heqs .D32
  have hD33 := heqs .D33
  have hD34 := heqs .D34
  have hD35 := heqs .D35
  have hD36 := heqs .D36
  have hD37 := heqs .D37
  simp only [ShortQuadratic.residual, expression, bExpr, AExpr, CExpr, QExpr,
    ShortQuadraticExpr.toPolynomial_sub, ShortQuadraticExpr.toPolynomial_pow,
    ShortQuadraticExpr.toPolynomial,
    MvPolynomial.eval_C, MvPolynomial.eval_X,
    MvPolynomial.eval_add, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, assignment, Nat.cast_one, Nat.cast_ofNat, sub_eq_zero] at hLamB hBSq hMod hAC₁ hCSmallSq hCFourth hQSq hQCube hQFourth hCQ hNSq hMU hPK hYK hAC hCSq hAE hFSq hGH hD2 hD3 hD4 hD5 hD6 hD8 hD9 hD10 hD16S hD16T hD17 hD18 hD19 hD20 hD21 hD22 hD23 hD26 hD27 hD30 hD31 hD32 hD33 hD34 hD35 hD36 hD37
  change (v .lamB : ℤ) = v .lam * v .B at hLamB
  have hbcast : (b : ℤ) = (v .epsilon : ℤ) + x := by simp [b]
  have hAcast : (A : ℤ) = (v .MU : ℤ) + v .M := by simp [A]
  have hCcast : (C : ℤ) = 2 * (v .R : ℤ) + 1 + v .C₁ + v .phi := by simp [C]
  have hgeom : (Q : ℤ) = 1 + v .lam * ((v .B : ℤ) - 1) := by
    simp only [Q, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub hBpos]
  have hQcast : (Q : ℤ) = 1 + (v .lamB : ℤ) - v .lam := by
    rw [hgeom, hLamB]
    ring
  simp only [← hbcast, ← hAcast, ← hCcast, ← hQcast] at hBSq hMod hAC₁ hQSq hQCube hQFourth hAC hCSq hAE hD3 hD5 hD8 hD16S hD16T hD17 hD21 hD30 hD35 hD36
  simp only [hLamB, hBSq, hMod, hAC₁, hCSmallSq, hCFourth, hQSq,
    hQCube, hQFourth, hCQ, hNSq, hMU, hPK, hYK, hAC, hCSq, hAE, hFSq, hGH] at hD2 hD3 hD4 hD8 hD16S hD16T hD17 hD18 hD19 hD20 hD21 hD26 hD27 hD30 hD32 hD33 hD34 hD35 hD37
  have hbase : v .B = shortBase ν z b := by
    have heq : (v .B : ℤ) = 2 * (b : ℤ) ^ 4 * (2 * (z : ℤ)) ^ (L4 ν + 1) := by
      linear_combination hD2
    unfold shortBase
    exact_mod_cast heq
  have hc : v .c = 1 + x * v .B + v .g := by exact_mod_cast hD6
  have hξ : (0 : ℤ) < v .xi := by exact_mod_cast hp .xi
  have hη : (0 : ℤ) < v .eta := by exact_mod_cast hp .eta
  have hsmall : v .e + 2 * z * b * v .l + 2 * z * v .B * v .c ^ 4 < 2 * z * Q := by
    have heq : (v .e : ℤ) + 2 * z * b * v .l +
        2 * z * v .B * (v .c : ℤ) ^ 4 < 2 * z * Q := by
      nlinarith only [hD8, hξ]
    exact_mod_cast heq
  have h4z : 4 * z < v .B := by rw [hbase]; exact shortBase_four_z_lt ν hz hb
  obtain ⟨_, hM0, _, _, hT20, _, hS30, _, hT30, _⟩ :=
    short_packing_bounds (Q := Q) hz hb h4z hlampos hlpos rfl hc hsmall
  have hbl : b * v .l < Q := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2 * z)
    nlinarith only [hsmall, Nat.zero_le (v .e), Nat.zero_le (2 * z * v .B * v .c ^ 4)]
  have hMpos : 0 < (Q : ℤ) - 1 - ((b : ℤ) - 1) * v .l := by
    have hblZ : (b : ℤ) * v .l < Q := by exact_mod_cast hbl
    have hlZ : (0 : ℤ) < v .l := by exact_mod_cast hlpos
    nlinarith only [hblZ, hlZ]
  have hB2z : (0 : ℤ) < (v .B : ℤ) - 2 * z := by
    have hnat : 2 * z < v .B := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hB2 : (0 : ℤ) < (v .B : ℤ) - 2 := by
    have hnat : 2 < v .B := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hT2pos : 0 < ((v .B : ℤ) - 2 * z) * v .lam * (1 + Q) := by positivity
  have hT3pos : 0 < ((v .B : ℤ) - 2) * Q := by positivity
  let M₁ := ((Q : ℤ) - 1 - ((b : ℤ) - 1) * v .l).toNat
  let S₃ := (shortS3 z (v .B) (v .c) (v .e) Q (v .lam)).toNat
  let T₂ := (((v .B : ℤ) - 2 * z) * v .lam * (1 + Q)).toNat
  let T₃ := (((v .B : ℤ) - 2) * Q).toNat
  have hMcast : (M₁ : ℤ) = (Q : ℤ) - 1 - ((b : ℤ) - 1) * v .l :=
    Int.toNat_of_nonneg hM0
  have hS3cast : (S₃ : ℤ) = shortS3 z (v .B) (v .c) (v .e) Q (v .lam) :=
    Int.toNat_of_nonneg hS30.le
  have hT2cast : (T₂ : ℤ) = ((v .B : ℤ) - 2 * z) * v .lam * (1 + Q) :=
    Int.toNat_of_nonneg hT20
  have hT3cast : (T₃ : ℤ) = ((v .B : ℤ) - 2) * Q := Int.toNat_of_nonneg hT30
  have hMnat : 0 < M₁ := by omega
  have hS3nat : 0 < S₃ := by
    have hposZ : (0 : ℤ) < S₃ := by rw [hS3cast]; exact hS30
    exact_mod_cast hposZ
  have hT2nat : 0 < T₂ := by omega
  have hT3nat : 0 < T₃ := by omega
  have hD24 : A = v .M * (v .U + 1) := by
    have hMUnat : v .MU = v .M * v .U := by exact_mod_cast hMU
    dsimp [A]
    rw [hMUnat]
    ring
  have hPell : ShortPellWitnesses (v .R) (v .N) b (v .B) (L4 ν) Q := by
    refine {
      A := A, C := C, C₁ := v .C₁, D := v .D, D₁ := v .D₁,
      E := v .E, F := v .F, G := v .G, H := v .H, I := v .I,
      K := v .K, M := v .M, P := v .P, U := v .U, V := 2,
      W := b * v .w, Y := v .Y, h := v .h, i := v .i, j := v .j,
      o := v .o, s := v .s, w := v .w, α := v .alpha,
      Δ := v .delta, γ := v .gamma, φ := v .phi,
      A_pos := hApos, C_pos := hCpos, C₁_pos := hp .C₁,
      D_pos := hp .D, D₁_pos := hp .D₁, E_pos := hp .E,
      F_pos := hp .F, G_pos := hp .G, H_pos := hp .H, I_pos := hp .I,
      K_pos := hp .K, M_pos := hp .M, P_pos := hp .P, U_pos := hp .U,
      V_pos := by norm_num, W_pos := Nat.mul_pos (by omega) (hp .w),
      Y_pos := hp .Y, h_pos := hp .h, i_pos := hp .i, j_pos := hp .j,
      o_pos := hp .o, s_pos := hp .s, w_pos := hp .w,
      α_pos := hp .alpha, Δ_pos := hp .delta, γ_pos := hp .gamma, φ_pos := hp .phi,
      D3 := by linear_combination hD3,
      D4 := by linear_combination hD4,
      D5 := hD5,
      D19 := ?_, D20 := ?_, D21 := by nlinarith only [hD21, hη],
      D22 := hD22, D23 := by exact_mod_cast hD23,
      D24 := hD24, D25 := rfl,
      D26 := by exact_mod_cast hD26, D27 := by exact_mod_cast hD27,
      D28 := rfl, D29 := rfl, D30 := ?_, D31 := by exact_mod_cast hD31,
      D32 := by linear_combination hD32, D33 := by exact_mod_cast hD33,
      D34 := by linear_combination hD34, D35 := hD35,
      D36 := by exact_mod_cast hD36, D37 := by linear_combination hD37
    }
    · have heq : (v .P : ℤ) = 2 * (v .M : ℤ) ^ 2 * v .U := by
        linear_combination hD19
      exact_mod_cast heq
    · refine ⟨(v .tau : ℤ), ?_⟩
      linear_combination hD20
    · push_cast
      linear_combination hD30
  refine ⟨{
    b := b, B := v .B, c := v .c, e := v .e, g := v .g,
    l := v .l, m := v .m, Q := Q, t := v .t, lam := v .lam,
    ε := v .epsilon, N := v .N, R := v .R, M₁ := M₁,
    D₀ := z * ((v .lam : ℤ) + Q) - v .e,
    S₁ := v .g, S₂ := v .l + v .e * Q, S₃ := S₃,
    T₁ := M₁, T₂ := T₂, T₃ := T₃,
    N₁ := Q, N₂ := 2 * z * Q ^ 2, N₃ := 8 * Q ^ 2,
    S := v .S, T := v .T, pell := hPell,
    b_pos := by omega, B_pos := hBpos, c_pos := hp .c, e_pos := hp .e,
    g_pos := hp .g, l_pos := hlpos, m_pos := hp .m, Q_pos := hQpos,
    t_pos := hp .t, lam_pos := hlampos, ε_pos := hp .epsilon,
    N_pos := hp .N, R_pos := hp .R, M₁_pos := hMnat,
    S₁_pos := hp .g, S₂_pos := by positivity, S₃_pos := hS3nat,
    T₁_pos := hMnat, T₂_pos := hT2nat, T₃_pos := hT3nat,
    N₁_pos := hQpos, N₂_pos := by positivity, N₃_pos := by positivity,
    S_pos := hp .S, T_pos := hp .T,
    D1 := rfl, D2 := hbase, D6 := hc, D7 := hgeom, D8 := hsmall,
    D9 := hD9, D10 := hD10, D11 := hMcast, D12 := rfl,
    D13 := ⟨rfl, rfl, rfl⟩, D14 := ⟨rfl, hT2cast, rfl⟩,
    D15 := ⟨hS3cast, hT3cast, rfl⟩, D16 := ⟨?_, ?_⟩,
    D17 := ?_, D18 := hD18
  }⟩
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hS3cast]
    dsimp [shortS3]
    linear_combination hD16S
  · apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hMcast, hT2cast, hT3cast]
    linear_combination hD16T
  · have heq : (v .N : ℤ) = (Q : ℤ) * (2 * z * (Q : ℤ) ^ 2) * (8 * (Q : ℤ) ^ 2) := by
      linear_combination hD17
    exact_mod_cast heq

end Jones1982.ShortQuadratic
