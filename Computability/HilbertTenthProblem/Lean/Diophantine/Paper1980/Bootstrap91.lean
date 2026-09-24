import Diophantine.Paper1980.System91
import Diophantine.Paper1980.TernaryMask

/-!
# Bootstrap bounds of the 91-operation tag certificate and the kernel conclusions

`EXPLORATION_PRODUCT_COORDINATE_TAG.md`, §2, and `EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`,
§2.  From positivity, the fixed-constant contract `Tag91.Ok` and the outer equations
alone:

* the integer width recovery: `3 ∣ R`, `3 ∣ q`, so `H ≡ 1 (mod 3)` and `C ∣ RH` forces
  `C ∣ R`; with `A = R/C` one has `R = CA`, `Z = AH` (`width_recovery91`);
* `q ≥ R ≥ C`, the marker bound `2 M₁ ≤ 3kH` from the length transport, and
  `M₁ ≤ jZ`, so that the packed word is positive in both leading branches and
  `q⁹ ≤ 2r`; and `r < q⁹`.

These are the hypotheses of the base-three kernel (`kernel3_sound`) at the scale
`D₀ = q⁹`: `U = 3^J`, `q` a power of three, `q⁹ ∣ C(2r, r)`; the unit-two mask then
gives the ternary digits of `r` and the Boolean packed word `P = r − rep(9e)`
(`2r + 1 = q⁹ + 2P`).
-/

namespace Jones1980

open Ternary

section Bounds

variable {T : Tag91} {Ninit Linit : ℕ}
  {Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ}
  (hT : T.Ok)
  (hP : Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hS : Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)

include hT

theorem three_le_Khalf : 3 ≤ T.Khalf := by
  obtain ⟨b, hb, hk⟩ := hT.Khalf_pow
  rw [hk]
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (b - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem three_dvd_Khalf : 3 ∣ T.Khalf := by
  obtain ⟨b, hb, hk⟩ := hT.Khalf_pow
  rw [hk]; exact dvd_pow_self 3 (by omega)

theorem three_le_B : 3 ≤ T.B := by
  obtain ⟨a, ha, hB⟩ := hT.B_pow
  rw [hB]
  calc 3 = 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem C_pos : 0 < T.C := by obtain ⟨g, hg⟩ := hT.C_pow; rw [hg]; positivity

/-- `j ≥ 12k`. -/
theorem jg_ge : 12 * T.Khalf ≤ T.jg := by
  have hk := three_le_Khalf hT
  have h1 := hT.jg_eq
  have h2 : T.C / (3 * T.Khalf) ≤ T.C / 9 := Nat.div_le_div_left (by omega) (by norm_num)
  have h3 : 9 * (T.C / 9) ≤ T.C := Nat.mul_div_le T.C 9
  have h4 := hT.C_gt_K3
  have h5 : T.Khalf ≤ T.Khalf ^ 3 := Nat.le_self_pow (by norm_num) _
  have h6 : (3 * T.Khalf) ^ 3 = 27 * T.Khalf ^ 3 := by ring
  omega

include hP hS

theorem R_ge91 : 3 ≤ R := by
  have h0 := hS.E0
  have hD := hP.D
  have : 3 * 1 ≤ T.Khalf * D := Nat.mul_le_mul (three_le_Khalf hT) hD
  omega

omit hT in
theorem R_le_q91 : R ≤ q := by rw [← hS.E5]; exact Nat.le_mul_of_pos_right _ hP.v

omit hT in
/-- `q ≤ RH`. -/
theorem q_le_RH91 : q ≤ R * H := by have := hS.E3; have := hP.H; omega

/-- The integer width recovery: `C ∣ R`, `R = CA`, `Z = AH`, `kD = CA`. -/
theorem width_recovery91 : ∃ A, 0 < A ∧ R = T.C * A ∧ Z = A * H ∧ T.Khalf * D = T.C * A := by
  have h3R : 3 ∣ R := by rw [← hS.E0]; exact Dvd.dvd.mul_right (three_dvd_Khalf hT) D
  have h3q : 3 ∣ q := by rw [← hS.E5]; exact Dvd.dvd.mul_right h3R v
  have hH : H % 3 = 1 := by
    have h3 := hS.E3
    obtain ⟨m, hm⟩ : 3 ∣ R * H := Dvd.dvd.mul_right h3R H
    obtain ⟨n, hn⟩ := h3q
    omega
  have hcop : Nat.Coprime T.C H := by
    obtain ⟨g, hg⟩ := hT.C_pow
    rw [hg]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  have hCR : T.C ∣ R := hcop.dvd_of_dvd_mul_right ⟨Z, hS.E4⟩
  obtain ⟨A, hA⟩ := hCR
  have hC0 := C_pos hT
  refine ⟨A, ?_, hA, ?_, by rw [hS.E0, hA]⟩
  · rcases Nat.eq_zero_or_pos A with h0 | h0
    · rw [h0, mul_zero] at hA; have := hP.R; omega
    · exact h0
  · have h4 := hS.E4
    rw [hA] at h4
    have : T.C * Z = T.C * (A * H) := by rw [← h4]; ring
    exact Nat.eq_of_mul_eq_mul_left hC0 this

theorem C_le_R91 : T.C ≤ R := by
  obtain ⟨A, hA0, hR, -, -⟩ := width_recovery91 hT hP hS
  rw [hR]; exact Nat.le_mul_of_pos_right _ hA0

theorem H_le_Z91 : H ≤ Z := by
  obtain ⟨A, hA0, -, hZ, -⟩ := width_recovery91 hT hP hS
  rw [hZ]; exact Nat.le_mul_of_pos_left _ hA0

/-- The marker bound `2 D M₁ ≤ 3q` from the length transport. -/
theorem marker_bound91 : 2 * D * (2 * Q + S1) ≤ 3 * q := by
  have h2 := hS.E2
  have hB : (3 : ℤ) ≤ T.B := by exact_mod_cast three_le_B hT
  have hD : (1 : ℤ) ≤ D := by exact_mod_cast hP.D
  have hM : (0 : ℤ) ≤ 2 * Q + S1 := by positivity
  have hL : (0 : ℤ) ≤ L := by positivity
  have hLi : (0 : ℤ) ≤ Linit := by positivity
  have hDM : (0 : ℤ) ≤ D * (2 * Q + S1) := by positivity
  have h3 : 2 * (D * (2 * Q + S1)) ≤ ((T.B : ℤ) - 1) * (D * (2 * Q + S1)) :=
    mul_le_mul_of_nonneg_right (by linarith) hDM
  have h4 : (L : ℤ) ≤ D * L := by nlinarith
  have : (2 * D * (2 * Q + S1) : ℤ) ≤ 3 * q := by nlinarith
  exact_mod_cast this

/-- `2 M₁ ≤ 3kH`. -/
theorem M1_bound91 : 2 * (2 * Q + S1) ≤ 3 * T.Khalf * H := by
  have h1 := marker_bound91 hT hP hS
  have h2 := q_le_RH91 hP hS
  have h0 := hS.E0
  have hD := hP.D
  have h3 : 2 * D * (2 * Q + S1) ≤ 3 * (T.Khalf * D * H) := by
    rw [h0]
    calc 2 * D * (2 * Q + S1) ≤ 3 * q := h1
      _ ≤ 3 * (R * H) := Nat.mul_le_mul_left 3 h2
  have h4 : D * (2 * (2 * Q + S1)) ≤ D * (3 * T.Khalf * H) := by
    calc D * (2 * (2 * Q + S1)) = 2 * D * (2 * Q + S1) := by ring
      _ ≤ 3 * (T.Khalf * D * H) := h3
      _ = D * (3 * T.Khalf * H) := by ring
  exact Nat.le_of_mul_le_mul_left h4 hD

/-- `M₁ ≤ jZ`, so the content field `N + jZ` is positive in both leading branches. -/
theorem M1_le_jZ91 : 2 * Q + S1 ≤ T.jg * Z := by
  have h1 := M1_bound91 hT hP hS
  have h2 := jg_ge hT
  have h3 := H_le_Z91 hT hP hS
  have h4 : 12 * T.Khalf * H ≤ T.jg * Z := by
    calc 12 * T.Khalf * H = (12 * T.Khalf) * H := by ring
      _ ≤ T.jg * Z := Nat.mul_le_mul h2 h3
  have h5 : 4 * (3 * T.Khalf * H) = 12 * T.Khalf * H := by ring
  omega

theorem GN_pos91 : (0 : ℤ) < T.N Q S1 Tc + T.jg * Z := by
  have h1 := M1_le_jZ91 hT hP hS
  have h1' : (2 * Q + S1 : ℤ) ≤ T.jg * Z := by exact_mod_cast h1
  have hT0 : (1 : ℤ) ≤ Tc := by exact_mod_cast hP.Tc
  unfold Tag91.N
  split_ifs <;> linarith

/-- The packed word is positive, so `q⁹ ≤ 2r`. -/
theorem r_lower91 : q ^ 9 ≤ 2 * r := by
  have h6 := hS.E6
  have hq : (1 : ℤ) ≤ q := by have := hP.q; exact_mod_cast this
  have hH : (1 : ℤ) ≤ H := by have := hP.H; exact_mod_cast this
  have hGN := GN_pos91 hT hP hS
  have hS1 : (0 : ℤ) ≤ S1 := by positivity
  have hQ : (0 : ℤ) ≤ Q := by positivity
  have hZ : (0 : ℤ) ≤ Z := by positivity
  have hL : (0 : ℤ) ≤ L := by positivity
  have hE : (0 : ℤ) ≤ E := by positivity
  have hcc : (0 : ℤ) ≤ T.cc := by positivity
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
  have hq2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 := by positivity
  have hq4 : (0 : ℤ) ≤ (q : ℤ) ^ 4 := by positivity
  have t1 : (0 : ℤ) ≤ ((q : ℤ) - 1) * S1 := mul_nonneg hq1 hS1
  have t2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 * (Q + q * (Q + Z)) := by positivity
  have t3 : (0 : ℤ) ≤ ((q : ℤ) - 1) * (2 * Q + S1) := mul_nonneg hq1 (by positivity)
  have t4 : (0 : ℤ) ≤ ((q : ℤ) - 1) * E := mul_nonneg hq1 hE
  have t5 : (0 : ℤ) ≤ (q : ℤ) ^ 2 * (T.N Q S1 Tc + T.jg * Z) := mul_nonneg hq2 hGN.le
  have t6 : (0 : ℤ) ≤ (q : ℤ) ^ 2 * (T.cc * H + ((q : ℤ) - 1) * E +
      (q : ℤ) ^ 2 * (T.N Q S1 Tc + T.jg * Z)) := mul_nonneg hq2 (by positivity)
  have t7 : (0 : ℤ) ≤ (q : ℤ) ^ 4 * ((L : ℤ) + ((q : ℤ) - 1) * (2 * Q + S1) +
      (q : ℤ) ^ 2 * (T.cc * H + ((q : ℤ) - 1) * E + (q : ℤ) ^ 2 * (T.N Q S1 Tc + T.jg * Z))) :=
    mul_nonneg hq4 (by positivity)
  have : ((q : ℤ) ^ 9 : ℤ) ≤ 2 * r := by linarith
  exact_mod_cast this

omit hT in
theorem r_lt91 : r < q ^ 9 := by have := hS.E7; have := hP.β; omega

theorem q_ge91 : 3 ≤ q := le_trans (R_ge91 hT hP hS) (R_le_q91 hP hS)

/-- The kernel conclusions: `q` is a power of three, `q⁹ ∣ C(2r, r)`, `U = 3^(2r+1)`. -/
theorem kernel_out91 :
    (∃ e, 1 ≤ e ∧ q = 3 ^ e) ∧ q ^ 9 ∣ (2 * r).choose r ∧ w * q ^ 9 = 3 ^ (2 * r + 1) := by
  have hA : 1 < a + 3 := by omega
  have hPp : 1 < 2 * (w * q ^ 9 * (s * q ^ 9) ^ 2) + 1 := by
    have : 0 < w * q ^ 9 * (s * q ^ 9) ^ 2 := by
      have := hP.kernel.w; have := hP.kernel.s; have := hP.q; positivity
    omega
  have hq := q_ge91 hT hP hS
  have hD0 : 81 ≤ q ^ 9 := by
    calc 81 ≤ 3 ^ 9 := by norm_num
      _ ≤ q ^ 9 := Nat.pow_le_pow_left hq 9
  have hr27 : 27 ≤ r := by have := r_lower91 hT hP hS; omega
  have hr2 : r < 2 * q ^ 9 := by have := r_lt91 hP hS; omega
  have out := kernel3_sound hP.kernel hS.kernel hD0 hr27 hr2 hA hPp
  refine ⟨?_, out.central, out.U_eq⟩
  have h1 : q ∣ 3 ^ (2 * r + 1) := by
    rw [← out.U_eq]; exact Dvd.intro_left (w * q ^ 8) (by ring)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  refine ⟨e, ?_, he⟩
  rcases Nat.eq_zero_or_pos e with h0 | h0
  · rw [h0, pow_zero] at he; omega
  · exact h0

/-- The masks: with `q = 3^e`, the ternary digits of `r` below `9e` are nonzero with unit
digit `2`, and the packed word `P = r − rep(9e)` is Boolean with unit digit `1`. -/
theorem mask91 :
    ∃ e, 1 ≤ e ∧ q = 3 ^ e ∧ q ^ 9 = 3 ^ (9 * e) ∧
      r % 3 = 2 ∧ (∀ i, 1 ≤ i → i < 9 * e → r / 3 ^ i % 3 ≠ 0) ∧
      rep (9 * e) ≤ r ∧ 2 * (r - rep (9 * e)) + q ^ 9 = 2 * r + 1 ∧
      (r - rep (9 * e)) % 3 = 1 ∧ ∀ i, (r - rep (9 * e)) / 3 ^ i % 3 ≤ 1 := by
  obtain ⟨⟨e, he1, he⟩, hcentral, -⟩ := kernel_out91 hT hP hS
  have hq9 : q ^ 9 = 3 ^ (9 * e) := by rw [he, ← pow_mul, mul_comm]
  have hr := r_lt91 hP hS
  rw [hq9] at hcentral hr
  have hN : 1 ≤ 9 * e := by omega
  obtain ⟨h0, hd⟩ := (ternary_mask hN hr).1 hcentral
  obtain ⟨hle, h1, hb⟩ := sub_rep hN hr h0 hd
  refine ⟨e, he1, he, hq9, h0, hd, hle, ?_, h1, hb⟩
  have := two_mul_rep_add_one (9 * e)
  rw [hq9]; omega

end Bounds

end Jones1980
