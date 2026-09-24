import Diophantine.Paper1982.ShortPellDefs

/-!
# Necessity for the polynomial Pell subsystem in Jones 1982, §5

Lemma 2.26 supplies the ratio witnesses and the smaller Pell value.
Lemma 2.28, with its alternate `F²−A` formula, supplies the large-index
Pell system. The two positive quotient theorems make both congruences
literal equations with positive witnesses, as required in (D3) and (D30).
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-- The central-binomial divisibility and two exponential relations have
the twenty-seven positive witnesses of (D3)–(D5), (D19)–(D37). -/
theorem exists_shortPell {R N b B L Q : ℕ}
    (hN : 8 ≤ N) (hb : 0 < b) (hbN : b ≤ N)
    (hchain : 3 < 3 * L ∧ 3 * L ≤ B ∧ B ≤ Q ∧ Q ≤ N ∧ N ≤ R)
    (hdvd : N ^ 2 ∣ (2 * R).choose R) (hpow : ∃ v, b = 2 ^ v)
    (hQ : Q = B ^ L) : Nonempty (ShortPellWitnesses R N b B L Q) := by
  obtain ⟨hL, hLB, hBQ, hQN, hNR⟩ := hchain
  have hR : 8 ≤ R := by omega
  have hbR : b ≤ R := by omega
  obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, Δ,
    hh, hs, hw, hφ, hC₁, hΔ, hcore, hW, hC₁index, hC₁psi⟩ :=
    exists_B26core (B₁ := L) false hR hN hbR hb hbN (by omega) (by omega) hdvd hpow
  change B25core R N b h s w (C₁ + φ) A B' C K M P U V W Y at hcore
  obtain ⟨hU64, hY64, hM512, hAbig, hA, _, _, hVpos, _, _⟩ :=
    hcore.sizes hR hN hs hw
  obtain ⟨_, _, _, hBA, _, _⟩ :=
    hcore.power_sizes hR hN hbN hs hw hL hLB hBQ hQN hNR
  have hCpos : 0 < C := by have := hcore.B7; have := hcore.B8; omega
  have hCpsi : C = ψ hA (2 * R + 1) := by rw [hcore.B14 hA, hcore.B7]
  have hC₁psiA : C₁ = ψ hA L := hC₁psi hA
  -- The smaller first coordinate and the positive quotient in (D3).
  let D₁ : ℕ := χ hA L
  have hD₁pos : 0 < D₁ := lt_of_le_of_lt (Nat.zero_le _) (yn_lt_xn hA L)
  obtain ⟨α, hα, hαeq⟩ :=
    exists_positive_pell_power_quotient_int (B := B) (L := L)
      hA (by omega) hBA (by omega : 2 ≤ L)
  have hQZ : (Q : ℤ) = (B : ℤ) ^ L := by exact_mod_cast hQ
  rw [← hQZ, ← hC₁psiA] at hαeq
  -- Choose the printed alternate formula for (D35).
  obtain ⟨D, E, F, G, H, I, i, j, hDpos, hFpos, hi, hj, hDI, hBH, hGalt, hPC⟩ :=
    exists_PConds hA (by omega : 1 < 2 * R + 1) false
  change G = A + F ^ 2 * (F ^ 2 - A) at hGalt
  rw [← hCpsi] at hPC
  -- The Pell pair pins the supplied `D` to the intended first coordinate.
  obtain ⟨n, hDn, hCn⟩ := eq_pell_of_sq hA hPC.P2
  have hn : n = 2 * R + 1 := (strictMono_y hA).injective (by rw [← hCn, hCpsi])
  have hDchi : D = χ hA (2 * R + 1) := by simpa only [hn] using hDn
  obtain ⟨γ, hγ, hγeq⟩ :=
    exists_positive_pell_quotient_int hA (by omega) (by omega : 2 ≤ 2 * R + 1)
  have hWZ : (W : ℤ) = 2 ^ (2 * R + 1) := by exact_mod_cast hW
  rw [← hDchi, ← hCpsi, ← hWZ] at hγeq
  -- The strict first-coordinate growth makes the quotient in (D31) positive.
  obtain ⟨o, hoeq⟩ := (Nat.modEq_iff_dvd' hDI.le).1 hPC.P1.symm
  have ho : 0 < o := by
    by_contra hnot
    have : o = 0 := by omega
    rw [this, mul_zero] at hoeq
    omega
  have hIeq : I = D + o * F := by rw [mul_comm o]; omega
  -- Positivity of the capitals and the bounds needed to cast subtraction.
  have hEpos : 0 < E := by rw [hPC.P3]; positivity
  have hG1 : 1 < G := by rw [hGalt]; omega
  have hHpos : 0 < H := by omega
  have hIpos : 0 < I := by omega
  have hKpos : 0 < K := by have := hcore.B4; omega
  have hPpos : 0 < P := by rw [hcore.B1]; positivity
  have hWpos : 0 < W := by rw [hcore.B11]; positivity
  have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA.le
  have hP2 : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ hPpos
  have hG2 : 1 ≤ G ^ 2 := Nat.one_le_pow _ _ hG1.le
  have hFA : A ≤ F ^ 2 := by
    have hterm : A ^ 2 - 1 ≤ (A ^ 2 - 1) * E ^ 2 :=
      Nat.le_mul_of_pos_right _ (pow_pos hEpos 2)
    have hAsq : A ≤ A ^ 2 := Nat.le_self_pow (by norm_num) A
    rw [hPC.P4]
    omega
  refine ⟨{
    A := A, C := C, C₁ := C₁, D := D, D₁ := D₁,
    E := E, F := F, G := G, H := H, I := I,
    K := K, M := M, P := P, U := U, V := V, W := W, Y := Y,
    h := h, i := i, j := j, o := o, s := s, w := w,
    α := α, Δ := Δ, γ := γ, φ := φ,
    A_pos := by omega, C_pos := hCpos, C₁_pos := hC₁,
    D_pos := hDpos, D₁_pos := hD₁pos, E_pos := hEpos, F_pos := hFpos,
    G_pos := by omega, H_pos := hHpos, I_pos := hIpos,
    K_pos := hKpos, M_pos := by omega, P_pos := hPpos,
    U_pos := by omega, V_pos := hVpos, W_pos := hWpos, Y_pos := by omega,
    h_pos := hh, i_pos := hi, j_pos := hj, o_pos := ho, s_pos := hs, w_pos := hw,
    α_pos := hα, Δ_pos := hΔ, γ_pos := hγ, φ_pos := hφ,
    D3 := ?_, D4 := ?_, D5 := ?_, D19 := hcore.B1, D20 := ?_, D21 := hcore.B3,
    D22 := ?_, D23 := hcore.B5, D24 := hcore.B6, D25 := ?_,
    D26 := hcore.B9, D27 := hcore.B10, D28 := hcore.B11, D29 := hcore.B12,
    D30 := ?_, D31 := hIeq, D32 := ?_, D33 := hPC.P3, D34 := ?_,
    D35 := ?_, D36 := hPC.P6, D37 := ?_
  }⟩
  · change (χ hA L : ℤ) = _
    linear_combination hαeq
  · have heq : D₁ ^ 2 = (A ^ 2 - 1) * C₁ ^ 2 + 1 := by
      rw [hC₁psiA]
      simpa only [D₁, pow_two, mul_assoc] using χ_sq hA L
    have heqZ := congrArg (fun n : ℕ => (n : ℤ)) heq
    push_cast [Nat.cast_sub hA2] at heqZ
    exact heqZ.symm
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hC₁index
    push_cast [Nat.cast_sub hA.le] at heqZ
    exact heqZ
  · have hsq := Int.isSquare_natCast_iff.mpr hcore.B2
    push_cast [Nat.cast_sub hP2] at hsq
    exact hsq
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hcore.B4
    push_cast [Nat.cast_sub hPpos] at heqZ
    exact heqZ
  · have h8 := hcore.B8
    rw [hcore.B7] at h8
    omega
  · rw [hcore.B12]
    linear_combination hγeq
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hPC.P2
    push_cast [Nat.cast_sub hA2] at heqZ
    exact heqZ
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hPC.P4
    push_cast [Nat.cast_sub hA2] at heqZ
    exact heqZ
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hGalt
    push_cast [Nat.cast_sub hFA] at heqZ
    exact heqZ
  · have heqZ := congrArg (fun n : ℕ => (n : ℤ)) hPC.P7
    push_cast [Nat.cast_sub hG2] at heqZ
    exact heqZ

end Jones1982
