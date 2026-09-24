import Diophantine.Paper1978.Lemma34
import Diophantine.Paper1978.BQT
import Diophantine.Paper1978.Bound
import Diophantine.Paper1976.Lemma23

/-!
# Jones 1978, Lemma 3.5: the Bounded Quantifier Theorem applied to Lemma 3.4

> **Lemma 3.5.** For positive integers `n, x`: `x ∈ Wₙ` iff there are nonnegative integers
> `b, e, g, h, q, r, s, u, v, w, β, π, θ` and integers `J, P, R, T, T₁, Z` with
> U0 `q = C(r,Z)`, `q ∣ C(b,Z), C(e,Z), C(g,Z), C(s,Z), C(w,Z)`; U1 `J(u,v) = n`;
> U2 `R = θ(1+β)`; U3 `M(u) ∣ hM(v) − x`; U4 `(hM(v) − R)² + x² < β`;
> U5 `T₁ = 3n`, `Z = T₁ + R³`; U6 `J = Z⁶`, `J³(J+2)(r+1)² + 1 = □`;
> U7 `T = R − eM(s)`, `P = R − bM(w)`; U8 `A(r)B(r)C(r)(T₁ + g − r) = qπ`.

`T₁, Z, J, R` are determined (`R ≥ 0` in every solution) and are substituted; `T, P` are
the integers `Tz` of Lemma 3.4.  The BQT is applied with the five unknowns `(g, b, e, s, w)`
(`g` first, as `U8` uses `T₁ + g − r`), `τ = 3n`, `z = Z` and the dominating function
`R(z) = z⁹⁰`.  The estimate `|A(y)B(y)C(y)| ≤ Z⁹⁰` for `y, b, e, g, s, w < Z` uses
`β < R` and `R³ ≤ Z` (`Bound.lean`); the article calls it "rather tedious" and omits it.
-/

namespace Jones1978

open Finset

/-- The polynomial of the BQT application: unknowns `(g, b, e, s, w)`. -/
def P35 (R β : ℕ) (y : ℕ) (zs : Fin 5 → ℕ) : ℤ :=
  Apoly R β y (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) * Bpoly R β y (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) *
    Cpoly (zs 0) y

/-- The conditions U0–U8 (with `Z = 3n + R³`, `J = Z⁶`, `T₁ = 3n`). -/
structure Cond35 (n x b e g h q r s u v w β π θ R : ℕ) : Prop where
  U0 : q = r.choose (3 * n + R ^ 3) ∧ q ∣ b.choose (3 * n + R ^ 3) ∧ q ∣ e.choose (3 * n + R ^ 3) ∧
    q ∣ g.choose (3 * n + R ^ 3) ∧ q ∣ s.choose (3 * n + R ^ 3) ∧ q ∣ w.choose (3 * n + R ^ 3)
  U1 : J u v = n
  U234 : U234 x u v h R β θ
  U6 : IsSquare (((3 * n + R ^ 3) ^ 6) ^ 3 * ((3 * n + R ^ 3) ^ 6 + 2) * (r + 1) ^ 2 + 1)
  U8 : Apoly R β r b e g s w * Bpoly R β r b e g s w * Cpoly g r * ((3 * n : ℤ) + g - r) = q * π

/-- U0–U8 with U8 weakened to the divisibility `q ∣ A(r)B(r)C(r)(T₁ + g − r)` (all that the
Bounded Quantifier Theorem needs; this is the form in which the system (1.3) yields it). -/
structure Cond35' (n x b e g h q r s u v w β θ R : ℕ) : Prop where
  U0 : q = r.choose (3 * n + R ^ 3) ∧ q ∣ b.choose (3 * n + R ^ 3) ∧ q ∣ e.choose (3 * n + R ^ 3) ∧
    q ∣ g.choose (3 * n + R ^ 3) ∧ q ∣ s.choose (3 * n + R ^ 3) ∧ q ∣ w.choose (3 * n + R ^ 3)
  U1 : J u v = n
  U234 : U234 x u v h R β θ
  U6 : IsSquare (((3 * n + R ^ 3) ^ 6) ^ 3 * ((3 * n + R ^ 3) ^ 6 + 2) * (r + 1) ^ 2 + 1)
  U8 : (q : ℤ) ∣ Apoly R β r b e g s w * Bpoly R β r b e g s w * Cpoly g r * ((3 * n : ℤ) + g - r)

theorem Cond35.weak {n x b e g h q r s u v w β π θ R : ℕ}
    (hc : Cond35 n x b e g h q r s u v w β π θ R) : Cond35' n x b e g h q r s u v w β θ R :=
  ⟨hc.U0, hc.U1, hc.U234, hc.U6, ⟨π, hc.U8⟩⟩

/-! ### Sizes from U2–U4 -/

/-- U2–U4 and `x > 0` give `2 ≤ β` and `β + 1 ≤ R` (so `θ ≥ 1`, `R ≥ 3`). -/
theorem sizes_of_U234 {x u v h R β θ : ℕ} (hx : 0 < x) (hU : U234 x u v h R β θ) :
    2 ≤ β ∧ β + 1 ≤ R := by
  obtain ⟨hU2, hU3, hU4⟩ := hU
  have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
  have hβ : (x : ℤ) ^ 2 < β := by have := sq_nonneg ((h : ℤ) * Mg β v - R); linarith
  have hβ2 : 2 ≤ β := by
    have : (1 : ℤ) < β := by nlinarith
    exact_mod_cast this
  refine ⟨hβ2, ?_⟩
  rcases Nat.eq_zero_or_pos θ with rfl | hθ
  · exfalso
    rw [zero_mul] at hU2
    subst hU2
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · -- `M(u) ∣ x` with `0 < x < M(u)`
      have hdvd : (Mg β u : ℤ) ∣ x := by
        have := hU3
        simp only [Nat.cast_zero, zero_mul, zero_sub] at this
        exact (dvd_neg).1 this
      have hMx : (Mg β u : ℤ) ≤ x := Int.le_of_dvd (by exact_mod_cast hx) hdvd
      have := Mg_ge β u
      have : (x : ℤ) ≤ x ^ 2 := by nlinarith
      linarith
    · -- `hM(v) ≥ 1 + β`, so `(hM(v))² ≥ 1 + β > β`
      have hM := Mg_ge β v
      have hh1 : (1 : ℤ) ≤ h := by exact_mod_cast hh
      have h1 : (1 + β : ℤ) ≤ h * Mg β v := by nlinarith
      have h2 : ((h : ℤ) * Mg β v - 0) ^ 2 ≥ h * Mg β v := by nlinarith
      have := sq_nonneg (x : ℤ)
      simp only [Nat.cast_zero] at hU4
      linarith
  · rw [hU2]
    have : 1 * (1 + β) ≤ θ * (1 + β) := Nat.mul_le_mul_right _ hθ
    omega

/-! ### The polynomial respects congruences -/

theorem P35_cong (R β : ℕ) : CongPreserving (P35 R β) := by
  intro p y y' z z' hy hz
  have hyZ : (y : ℤ) ≡ y' [ZMOD p] := Int.natCast_modEq_iff.2 hy
  have h0 : ((z 0 : ℕ) : ℤ) ≡ z' 0 [ZMOD p] := Int.natCast_modEq_iff.2 (hz 0)
  have h1 : ((z 1 : ℕ) : ℤ) ≡ z' 1 [ZMOD p] := Int.natCast_modEq_iff.2 (hz 1)
  have h2 : ((z 2 : ℕ) : ℤ) ≡ z' 2 [ZMOD p] := Int.natCast_modEq_iff.2 (hz 2)
  have h3 : ((z 3 : ℕ) : ℤ) ≡ z' 3 [ZMOD p] := Int.natCast_modEq_iff.2 (hz 3)
  have h4 : ((z 4 : ℕ) : ℤ) ≡ z' 4 [ZMOD p] := Int.natCast_modEq_iff.2 (hz 4)
  unfold P35 Apoly Bpoly Cpoly Tz Mz
  gcongr

/-! ### The estimate `|A(y)B(y)C(y)| ≤ Z⁹⁰` -/

set_option maxHeartbeats 2000000 in
/-- The domination estimate at `z = Z = 3n + R³`, for `β < R`, `3 ≤ R`. -/
theorem P35_dominates {n R β : ℕ} (hn : 0 < n) (hR3 : 3 ≤ R) (hβR : β + 1 ≤ R) :
    DominatesAt (P35 R β) (fun z => z ^ 90) (3 * n + R ^ 3) := by
  intro y zs hy hzs
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℤ, Z = ((3 * n + R ^ 3 : ℕ) : ℤ) := ⟨_, rfl⟩
  have hR1 : (1 : ℤ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hR3Z : (R : ℤ) ^ 3 ≤ Z := by rw [hZdef]; push_cast; linarith [(by positivity : (0 : ℤ) ≤ 3 * n)]
  have hRZ : (R : ℤ) ≤ Z := by
    have : (R : ℤ) ≤ R ^ 3 := by
      have h := pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)
      simpa using h
    linarith
  have hZ30 : (30 : ℤ) ≤ Z := by
    have : (27 : ℤ) ≤ R ^ 3 := by
      have : (3 : ℤ) ≤ R := by exact_mod_cast hR3
      calc (27 : ℤ) = 3 ^ 3 := by norm_num
        _ ≤ R ^ 3 := pow_le_pow_left₀ (by norm_num) this 3
    rw [hZdef]; push_cast
    have : (1 : ℤ) ≤ n := by exact_mod_cast hn
    linarith
  have hZ0 : (0 : ℤ) ≤ Z := by linarith
  -- the atoms
  have hyZ : |(y : ℤ)| ≤ Z := by
    rw [abs_of_nonneg (by positivity), hZdef]; exact_mod_cast hy.le
  have hzZ : ∀ i, |((zs i : ℕ) : ℤ)| ≤ Z := fun i => by
    rw [abs_of_nonneg (by positivity), hZdef]; exact_mod_cast (hzs i).le
  have hβ : |(β : ℤ)| ≤ R := by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast (show β ≤ R by omega)
  have hRR : |(R : ℤ)| ≤ R := by rw [abs_of_nonneg (by positivity)]
  have c1 : |(1 : ℤ)| ≤ ((1 : ℕ) : ℤ) := by norm_num
  have c2 : |(2 : ℤ)| ≤ ((2 : ℕ) : ℤ) := by norm_num
  have c3 : |(3 : ℤ)| ≤ ((3 : ℕ) : ℤ) := by norm_num
  have c9 : |(9 : ℤ)| ≤ ((9 : ℕ) : ℤ) := by norm_num
  -- names for the unknowns
  set b := zs 1
  set e := zs 2
  set g := zs 0
  set s := zs 3
  set w := zs 4
  have hb := hzZ 1
  have he := hzZ 2
  have hg := hzZ 0
  have hs := hzZ 3
  have hw := hzZ 4
  -- `M(t) = 1 + (1 + t) β`
  have hM : ∀ t : ℕ, |(t : ℤ)| ≤ Z → Bd Z R 3 1 1 (Mz β t) := fun t ht => by
    unfold Mz
    exact Bd.add hR1 hRZ (Bd.const c1) (Bd.mul hR1 hRZ (Bd.add hR1 hRZ (Bd.const c1) (Bd.ofZ ht))
      (Bd.ofR hβ))
  have hMy := hM y hyZ
  have hMs := hM s hs
  have hMw := hM w hw
  -- `T = R − e M(s)`, `P = R − b M(w)`
  have hT : Bd Z R 4 2 1 (Tz R β e s) := by
    unfold Tz
    exact Bd.sub hR1 hRZ (Bd.ofR hRR) (Bd.mul hR1 hRZ (Bd.ofZ he) hMs)
  have hP : Bd Z R 4 2 1 (Tz R β b w) := by
    unfold Tz
    exact Bd.sub hR1 hRZ (Bd.ofR hRR) (Bd.mul hR1 hRZ (Bd.ofZ hb) hMw)
  have hTsq := Bd.sq hR1 hRZ hT
  have hPsq := Bd.sq hR1 hRZ hP
  -- `w' = β − T² − P²`
  have hw' := Bd.sub hR1 hRZ (Bd.sub hR1 hRZ (Bd.ofR hβ) hTsq) hPsq
  have hMy2 := Bd.sq hR1 hRZ hMy
  have hg1 := Bd.add hR1 hRZ (Bd.ofZ hg) (Bd.const c1)
  have hgM := Bd.mul hR1 hRZ hg1 hMy2
  -- `A(y)`
  have hv1 := Bd.sub hR1 hRZ (Bd.sub hR1 hRZ (Bd.ofR hRR) hT) hP
  have hv1sq := Bd.sq hR1 hRZ hv1
  have h1v1 := Bd.add hR1 hRZ (Bd.const c1) hv1sq
  have hbrA := Bd.sub hR1 hRZ (Bd.sub hR1 hRZ (Bd.mul hR1 hRZ (Bd.mul hR1 hRZ hMy2 h1v1) hw') hv1sq) hgM
  have hbrAsq := Bd.sq hR1 hRZ hbrA
  have hsw := Bd.add hR1 hRZ (Bd.ofZ hs) (Bd.ofZ hw)
  have hfA := Bd.sub hR1 hRZ (Bd.add hR1 hRZ (Bd.add hR1 hRZ (Bd.mul hR1 hRZ (Bd.const c3)
    (Bd.sq hR1 hRZ hsw)) (Bd.mul hR1 hRZ (Bd.const c9) (Bd.ofZ hw)))
    (Bd.mul hR1 hRZ (Bd.const c3) (Bd.ofZ hs))) (Bd.mul hR1 hRZ (Bd.const c2) (Bd.ofZ hyZ))
  have hA := Bd.add hR1 hRZ (Bd.sq hR1 hRZ hfA) hbrAsq
  -- `B(y)`
  have hTP := Bd.mul hR1 hRZ hT hP
  have hv2 := Bd.sub hR1 hRZ (Bd.ofR hRR) hTP
  have hv2sq := Bd.sq hR1 hRZ hv2
  have h1v2 := Bd.add hR1 hRZ (Bd.const c1) hv2sq
  have hbrB := Bd.sub hR1 hRZ (Bd.sub hR1 hRZ (Bd.mul hR1 hRZ (Bd.mul hR1 hRZ hMy2 h1v2) hw') hv2sq) hgM
  have hbrBsq := Bd.sq hR1 hRZ hbrB
  have hfB := Bd.sub hR1 hRZ (Bd.add hR1 hRZ (Bd.add hR1 hRZ (Bd.add hR1 hRZ (Bd.mul hR1 hRZ (Bd.const c3)
    (Bd.sq hR1 hRZ hsw)) (Bd.mul hR1 hRZ (Bd.const c9) (Bd.ofZ hw)))
    (Bd.mul hR1 hRZ (Bd.const c3) (Bd.ofZ hs))) (Bd.const c2)) (Bd.mul hR1 hRZ (Bd.const c2) (Bd.ofZ hyZ))
  have hB := Bd.add hR1 hRZ (Bd.sq hR1 hRZ hfB) hbrBsq
  -- `C(y)`
  have hC := Bd.sub hR1 hRZ (Bd.add hR1 hRZ (Bd.mul hR1 hRZ (Bd.const c3) (Bd.ofZ hg)) (Bd.const c2))
    (Bd.ofZ hyZ)
  have hABC := Bd.mul hR1 hRZ (Bd.mul hR1 hRZ hA hB) hC
  have key := Bd.to_pow hR1 hR3Z hZ30 hABC 14 90 (by decide) (by decide)
  show |P35 R β y zs| ≤ (((3 * n + R ^ 3) ^ 90 : ℕ) : ℤ)
  have hZ' : (((3 * n + R ^ 3) ^ 90 : ℕ) : ℤ) = Z ^ 90 := by rw [hZdef]; push_cast; ring
  rw [hZ']
  unfold P35 Apoly Bpoly Cpoly
  exact key

/-! ### The numeric inequality for condition (iii) -/

/-- For `Z ≥ 30`: `(2 Z Z! Z⁹⁰)^(Z⁵) + Z ≤ Z⁶ − 1 + (Z⁶)^(Z⁶ − 2)`. -/
theorem numeric_iii {Z : ℕ} (hZ : 30 ≤ Z) :
    (2 * Z * Z.factorial * Z ^ 90) ^ (Z ^ 5) + Z ≤ Z ^ 6 - 1 + (Z ^ 6) ^ (Z ^ 6 - 2) := by
  have hZ1 : 1 ≤ Z := by omega
  have h1 : 2 * Z * Z.factorial * Z ^ 90 ≤ Z ^ (Z + 92) := by
    have hf : Z.factorial ≤ Z ^ Z := Nat.factorial_le_pow Z
    have h2Z : 2 * Z ≤ Z ^ 2 := by nlinarith
    calc 2 * Z * Z.factorial * Z ^ 90 ≤ Z ^ 2 * Z ^ Z * Z ^ 90 :=
          Nat.mul_le_mul (Nat.mul_le_mul h2Z hf) le_rfl
      _ = Z ^ (Z + 92) := by rw [← pow_add, ← pow_add]; congr 1; ring
  have h2 : (Z ^ (Z + 92)) ^ (Z ^ 5) = Z ^ ((Z + 92) * Z ^ 5) := by rw [← pow_mul]
  have h3 : (Z ^ 6) ^ (Z ^ 6 - 2) = Z ^ (6 * (Z ^ 6 - 2)) := by rw [← pow_mul]
  -- exponent comparison: `(Z + 92) Z⁵ + 1 ≤ 6 (Z⁶ − 2)`
  have hZ6 : 2 ≤ Z ^ 6 := by
    calc 2 ≤ 30 ^ 6 := by norm_num
      _ ≤ Z ^ 6 := Nat.pow_le_pow_left hZ 6
  have hexp : (Z + 92) * Z ^ 5 + 1 ≤ 6 * (Z ^ 6 - 2) := by
    have hZ5 : 30 ^ 5 ≤ Z ^ 5 := Nat.pow_le_pow_left hZ 5
    have h6 : Z ^ 6 = Z * Z ^ 5 := by ring
    have h7 : 6 * (Z ^ 6 - 2) = 6 * Z ^ 6 - 12 := by omega
    rw [h7, h6]
    have : (Z + 92) * Z ^ 5 = Z * Z ^ 5 + 92 * Z ^ 5 := by ring
    rw [this]
    have h8 : 150 * Z ^ 5 ≤ 5 * (Z * Z ^ 5) := by nlinarith
    omega
  have hpow : Z ^ ((Z + 92) * Z ^ 5) + Z ≤ Z ^ (6 * (Z ^ 6 - 2)) := by
    have hA1 : 1 ≤ Z ^ ((Z + 92) * Z ^ 5) := Nat.one_le_pow _ _ hZ1
    have hZle : Z ≤ Z ^ ((Z + 92) * Z ^ 5) := Nat.le_self_pow (by positivity) Z
    calc Z ^ ((Z + 92) * Z ^ 5) + Z ≤ Z ^ ((Z + 92) * Z ^ 5) * Z := by nlinarith
      _ = Z ^ ((Z + 92) * Z ^ 5 + 1) := (pow_succ Z _).symm
      _ ≤ Z ^ (6 * (Z ^ 6 - 2)) := Nat.pow_le_pow_right hZ1 hexp
  calc (2 * Z * Z.factorial * Z ^ 90) ^ (Z ^ 5) + Z ≤ (Z ^ (Z + 92)) ^ (Z ^ 5) + Z := by
        have := Nat.pow_le_pow_left h1 (Z ^ 5); omega
    _ = Z ^ ((Z + 92) * Z ^ 5) + Z := by rw [h2]
    _ ≤ Z ^ (6 * (Z ^ 6 - 2)) := hpow
    _ = (Z ^ 6) ^ (Z ^ 6 - 2) := h3.symm
    _ ≤ Z ^ 6 - 1 + (Z ^ 6) ^ (Z ^ 6 - 2) := Nat.le_add_left _ _

/-! ### Lemma 3.5 -/

/-- Sufficiency: U0–U8 (with the weak U8) ⟹ `x ∈ Wₙ`. -/
theorem mem_of_cond35' {n x b e g h q r s u v w β θ R : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hc : Cond35' n x b e g h q r s u v w β θ R) : x ∈ W n := by
  obtain ⟨hβ2, hβR⟩ := sizes_of_U234 hx hc.U234
  have hR3 : 3 ≤ R := by omega
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 3 * n + R ^ 3 := ⟨_, rfl⟩
  have hZ30 : 30 ≤ Z := by
    have : 27 ≤ R ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ R ^ 3 := Nat.pow_le_pow_left hR3 3
    omega
  -- the BQT conditions
  obtain ⟨hq, hqb, hqe, hqg, hqs, hqw⟩ := hc.U0
  rw [← hZ] at hq hqb hqe hqg hqs hqw
  have hU6 := hc.U6
  rw [← hZ] at hU6
  obtain ⟨sq, hsq⟩ := hU6
  have hJ2 : 2 ≤ Z ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hZ30 6)
  have hr := JSWW1976.lemma_2_3 hJ2 hsq
  have hiii : (2 * Z * Z.factorial * Z ^ 90) ^ (Z ^ (4 + 1)) + Z ≤ r :=
    le_trans (numeric_iii hZ30) hr
  have hconds : BQTConds (P35 R β) (fun z => z ^ 90) (3 * n) Z r ![g, b, e, s, w] :=
    { z_pos := by omega
      i := by
        have hU8 := hc.U8
        rw [hq] at hU8
        simp only [P35, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four]
        push_cast
        exact hU8
      ii := by omega
      iii := hiii
      iv := by
        intro i
        fin_cases i <;> simp <;> [exact hq ▸ hqg; exact hq ▸ hqb; exact hq ▸ hqe; exact hq ▸ hqs;
          exact hq ▸ hqw] }
  have hdom : DominatesAt (P35 R β) (fun z => z ^ 90) Z := by
    rw [hZ]; exact P35_dominates hn hR3 hβR
  have hall := bqt_sufficiency (P35_cong R β) hdom hconds
  -- Lemma 3.4
  apply (lemma_3_4 hn hx).2
  refine ⟨u, v, h, R, β, θ, hc.U1, hc.U234, fun y hy => ?_⟩
  obtain ⟨zs, hzs⟩ := hall y hy
  exact ⟨zs 1, zs 2, zs 0, zs 3, zs 4, hzs⟩

theorem mem_of_cond35 {n x b e g h q r s u v w β π θ R : ℕ} (hn : 0 < n) (hx : 0 < x)
    (hc : Cond35 n x b e g h q r s u v w β π θ R) : x ∈ W n :=
  mem_of_cond35' hn hx hc.weak

/-- Necessity: `x ∈ Wₙ` ⟹ U0–U8 are satisfiable, with moreover `(Z!)² ∣ r + 1`
(needed to pass from U0 to B0–B8 in Theorem 3). -/
theorem cond35_of_mem' {n x : ℕ} (hn : 0 < n) (hx : 0 < x) (hW : x ∈ W n) :
    ∃ b e g h q r s u v w β π θ R, Cond35 n x b e g h q r s u v w β π θ R ∧
      ((3 * n + R ^ 3).factorial) ^ 2 ∣ r + 1 ∧ r ≤ g := by
  classical
  obtain ⟨u, v, h, R, β, θ, hJ, hU, hwit⟩ := cond34_of_mem_bounded hn hx hW
  obtain ⟨hβ2, hβR⟩ := sizes_of_U234 hx hU
  have hR3 : 3 ≤ R := by omega
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = 3 * n + R ^ 3 := ⟨_, rfl⟩
  have hZ30 : 30 ≤ Z := by
    have : 27 ≤ R ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ R ^ 3 := Nat.pow_le_pow_left hR3 3
    omega
  -- `r` from the converse of Lemma 2.4 with `(Z!)² ∣ r + 1`
  have hJ1 : 1 ≤ Z ^ 6 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨r, sq, hsq, hdvd⟩ := JSWW1976.lemma_2_3_converse hJ1
    (show 1 ≤ Z.factorial ^ 2 from Nat.one_le_pow _ _ (Nat.factorial_pos Z))
  have hJ2 : 2 ≤ Z ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hZ30 6)
  have hrZ : Z ≤ r := by
    have := JSWW1976.lemma_2_3 hJ2 hsq
    have h1 : Z ≤ Z ^ 6 := Nat.le_self_pow (by norm_num) Z
    have h2 : 1 ≤ (Z ^ 6) ^ (Z ^ 6 - 2) := Nat.one_le_pow _ _ (by positivity)
    omega
  -- witnesses as functions `ℕ → Fin 5 → ℕ`
  have hw' : ∀ y, ∃ zs : Fin 5 → ℕ, y < 3 * n → (P35 R β y zs = 0 ∧ ∀ i, zs i < Z) := by
    intro y
    by_cases hy : y < 3 * n
    · obtain ⟨b, e, g, s, w, hb, he, hg, hs, hw, hABC⟩ := hwit y hy
      refine ⟨![g, b, e, s, w], fun _ => ⟨?_, ?_⟩⟩
      · simp only [P35, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four]
        exact hABC
      · intro i; fin_cases i <;> simp <;> omega
    · exact ⟨fun _ => 0, fun h => absurd h hy⟩
  choose wf hwf using hw'
  obtain ⟨zs, hi, hiv, hN⟩ := bqt_necessity_core (P35_cong R β) (τ := 3 * n) (by omega)
    (by omega) hrZ hdvd wf (fun y hy => (hwf y hy).1) (fun y hy => (hwf y hy).2) r
  -- the product in U8 is nonnegative since `g ≥ r`
  have hg := hN 0
  have hprod : 0 ≤ Apoly R β r (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) *
      Bpoly R β r (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) * Cpoly (zs 0) r * ((3 * n : ℤ) + zs 0 - r) := by
    have hA : 0 ≤ Apoly R β r (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) := by unfold Apoly; positivity
    have hB : 0 ≤ Bpoly R β r (zs 1) (zs 2) (zs 0) (zs 3) (zs 4) := by unfold Bpoly; positivity
    have hC : 0 ≤ Cpoly (zs 0) r := by
      unfold Cpoly
      have : (r : ℤ) ≤ zs 0 := by exact_mod_cast hg
      linarith
    have hD : 0 ≤ (3 * n : ℤ) + zs 0 - r := by
      have : (r : ℤ) ≤ zs 0 := by exact_mod_cast hg
      linarith
    positivity
  obtain ⟨π, hπ⟩ := hi
  simp only [P35] at hπ
  rw [show ((3 * n : ℕ) : ℤ) = (3 * n : ℤ) by push_cast; ring] at hπ
  have hπ0 : 0 ≤ π := by
    have hq : (0 : ℤ) < r.choose Z := by exact_mod_cast Nat.choose_pos hrZ
    rw [hπ] at hprod
    by_contra hneg
    push Not at hneg
    have : (r.choose Z : ℤ) * π < 0 := mul_neg_of_pos_of_neg hq hneg
    linarith
  refine ⟨zs 1, zs 2, zs 0, h, r.choose Z, r, zs 3, u, v, zs 4, β, π.toNat, θ, R,
    ⟨?_, hJ, hU, ?_, ?_⟩, by rw [← hZ]; exact hdvd, hg⟩
  · rw [← hZ]
    exact ⟨rfl, hiv 1, hiv 2, hiv 0, hiv 3, hiv 4⟩
  · rw [← hZ]; exact ⟨sq, hsq⟩
  · rw [Int.toNat_of_nonneg hπ0]
    exact hπ

theorem cond35_of_mem {n x : ℕ} (hn : 0 < n) (hx : 0 < x) (hW : x ∈ W n) :
    ∃ b e g h q r s u v w β π θ R, Cond35 n x b e g h q r s u v w β π θ R := by
  obtain ⟨b, e, g, h, q, r, s, u, v, w, β, π, θ, R, hc, -, -⟩ := cond35_of_mem' hn hx hW
  exact ⟨b, e, g, h, q, r, s, u, v, w, β, π, θ, R, hc⟩

/-- **Lemma 3.5.** -/
theorem lemma_3_5 {n x : ℕ} (hn : 0 < n) (hx : 0 < x) :
    x ∈ W n ↔ ∃ b e g h q r s u v w β π θ R, Cond35 n x b e g h q r s u v w β π θ R :=
  ⟨cond35_of_mem hn hx, fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ => mem_of_cond35 hn hx hc⟩

end Jones1978
