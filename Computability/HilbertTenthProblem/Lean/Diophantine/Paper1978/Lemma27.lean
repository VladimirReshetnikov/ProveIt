import Diophantine.Paper1978.Binomial
import Diophantine.Paper1976.Lemma23

/-!
# Jones 1978, Lemma 2.7: the binomial conditions U0 from a single partial binomial

> **Lemma 2.7.** For `z! + 6 < r`, if `z! ∣ r + 1` and U0 holds, then B0–B8 can be
> satisfied.  Conversely B0–B8 imply U0.  Furthermore B1–B7 and `z! + 6 < r` imply
> `z < N`, `1 < Y` and `8 N^z < X`.

U0: `q = C(r, z)`, `q ∣ C(zᵢ, z)` (`i = 1, …, n`).

B0 `Y = ⌊(X+1)^N / X^z⌋`; B1 `W = r + q + Σ zᵢ + Σ bᵢ`; B2 `W³(W+2)(σ+1)² + 1 = □`;
B3 `N = σ(r+1)`; B4 `N ≡ zᵢ (mod σ + dᵢ)`; B5 `N³(N+2)(ζ+1)² + 1 = □`;
B6 `X = ζ(N − r)(σ+d₁)⋯(σ+dₙ)`; B7 `Y = q + (ξ+1)(N − r)`; B8 `Y = q bᵢ + cᵢ(σ + dᵢ)`.

Lemma 2.4 is `JSWW1976.lemma_2_3` (with its converse).
-/

namespace Jones1978

open Finset

variable {n : ℕ}

/-- The conditions U0. -/
def U0 (z r q : ℕ) (zs : Fin n → ℕ) : Prop := q = r.choose z ∧ ∀ i, q ∣ (zs i).choose z

/-- The conditions B0–B8. -/
structure BConds (z r q : ℕ) (zs : Fin n → ℕ) (W σ N ζ X Y ξ : ℕ) (b c d : Fin n → ℕ) :
    Prop where
  B0 : Y = (X + 1) ^ N / X ^ z
  B1 : W = r + q + ∑ i, zs i + ∑ i, b i
  B2 : IsSquare (W ^ 3 * (W + 2) * (σ + 1) ^ 2 + 1)
  B3 : N = σ * (r + 1)
  B4 : ∀ i, N ≡ zs i [MOD σ + d i]
  B5 : IsSquare (N ^ 3 * (N + 2) * (ζ + 1) ^ 2 + 1)
  B6 : X = ζ * (N - r) * ∏ i, (σ + d i)
  B7 : Y = q + (ξ + 1) * (N - r)
  B8 : ∀ i, Y = q * b i + c i * (σ + d i)

/-! ### Size estimates shared by both directions -/

/-- The estimates (9), (10) and `N > σ > r > z + 2`, `8 N^z < N^(N−2) ≤ ζ`. -/
structure Bounds (z r W σ N ζ : ℕ) : Prop where
  W8 : 8 ≤ W
  zW : z + 7 ≤ W
  W2 : W ^ 2 < W ^ (W - 2)
  W3 : W ^ 3 < W ^ (W - 2)
  Wz : W ^ z < W ^ (W - 2)
  rσ : r < σ
  σN : σ < N
  zN3 : z + 3 ≤ N
  N9 : 9 ≤ N
  eightN : 8 * N ^ z < N ^ (N - 2)
  ζ_ge : N ^ (N - 2) ≤ ζ

theorem bounds {z r W σ N ζ : ℕ} (hr : z.factorial + 6 < r) (hrW : r ≤ W)
    (hσ : W - 1 + W ^ (W - 2) ≤ σ) (hN : N = σ * (r + 1)) (hζ : N - 1 + N ^ (N - 2) ≤ ζ) :
    Bounds z r W σ N ζ := by
  have hzf : z ≤ z.factorial := Nat.self_le_factorial z
  have hf1 : 1 ≤ z.factorial := Nat.factorial_pos z
  have hW8 : 8 ≤ W := by omega
  have hzW : z + 7 ≤ W := by omega
  have hWpow : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
  have hrσ : r < σ := by omega
  have hσN : σ < N := by rw [hN]; nlinarith
  have hzN3 : z + 3 ≤ N := by omega
  have hN9 : 9 ≤ N := by omega
  refine ⟨hW8, hzW, Nat.pow_lt_pow_right (by omega) (by omega),
    Nat.pow_lt_pow_right (by omega) (by omega), Nat.pow_lt_pow_right (by omega) (by omega),
    hrσ, hσN, hzN3, hN9, ?_, by omega⟩
  calc 8 * N ^ z ≤ 8 * N ^ (N - 3) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ < N * N ^ (N - 3) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = N ^ (N - 2) := by rw [← pow_succ']; congr 1; omega

/-- From `a ≡ b (mod m)`, `a, b < m`: `a = b`, where `m = d / gcd d z!` and
`z! a < d`, `z! b < d`. -/
theorem eq_of_modEq_div_gcd {d z a b : ℕ} (hd : 0 < d)
    (h : a ≡ b [MOD d / Nat.gcd d z.factorial]) (ha : z.factorial * a < d)
    (hb : z.factorial * b < d) : a = b := by
  set g := Nat.gcd d z.factorial with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hgf : g ≤ z.factorial := Nat.le_of_dvd (Nat.factorial_pos z) (Nat.gcd_dvd_right _ _)
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left d z.factorial
  rw [← hg] at hm
  have hdm : d / g = m := by rw [hm, Nat.mul_div_cancel_left _ hgpos]
  rw [hdm] at h
  apply Nat.ModEq.eq_of_lt_of_lt h
  · have : a * g < g * m := by
      calc a * g ≤ a * z.factorial := Nat.mul_le_mul_left _ hgf
        _ < d := by rw [mul_comm]; exact ha
        _ = g * m := hm
    rw [mul_comm g] at this
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  · have : b * g < g * m := by
      calc b * g ≤ b * z.factorial := Nat.mul_le_mul_left _ hgf
        _ < d := by rw [mul_comm]; exact hb
        _ = g * m := hm
    rw [mul_comm g] at this
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)

/-- The size facts from B1, B2, B3, B5, B6, B7 alone (without B0): `z < N`, `1 < Y`,
`8 N^z < X`; also `r < σ < N`. -/
theorem sizes_of_B {z r q : ℕ} {zs : Fin n → ℕ} {W σ N ζ X Y ξ : ℕ} {b d : Fin n → ℕ}
    (hr : z.factorial + 6 < r)
    (B1 : W = r + q + ∑ i, zs i + ∑ i, b i)
    (B2 : IsSquare (W ^ 3 * (W + 2) * (σ + 1) ^ 2 + 1))
    (B3 : N = σ * (r + 1))
    (B5 : IsSquare (N ^ 3 * (N + 2) * (ζ + 1) ^ 2 + 1))
    (B6 : X = ζ * (N - r) * ∏ i, (σ + d i))
    (B7 : Y = q + (ξ + 1) * (N - r)) :
    z < N ∧ 1 < Y ∧ 8 * N ^ z < X ∧ r < σ ∧ σ < N := by
  have hzf : z ≤ z.factorial := Nat.self_le_factorial z
  have hrW : r ≤ W := by rw [B1]; omega
  obtain ⟨x, hx⟩ := B2
  have hσ : W - 1 + W ^ (W - 2) ≤ σ := JSWW1976.lemma_2_3 (by omega) hx
  obtain ⟨x', hx'⟩ := B5
  have hσ7 : 7 ≤ σ := by
    have : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
    omega
  have hζ : N - 1 + N ^ (N - 2) ≤ ζ := JSWW1976.lemma_2_3 (by rw [B3]; nlinarith) hx'
  have bd := bounds hr hrW hσ B3 hζ
  have hrσ := bd.rσ
  have hσN := bd.σN
  have hζX : ζ ≤ X := by
    rw [B6]
    have h1 : 1 ≤ N - r := by omega
    have h2 : 1 ≤ ∏ i, (σ + d i) :=
      Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => by omega))
    calc ζ = ζ * 1 * 1 := by ring
      _ ≤ ζ * (N - r) * ∏ i, (σ + d i) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have h8X : 8 * N ^ z < X := by have := bd.eightN; have := bd.ζ_ge; omega
  have hzN : z < N := by have := bd.zN3; omega
  have hY : 1 < Y := by
    rw [B7]
    have : N - r ≤ (ξ + 1) * (N - r) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact ⟨hzN, hY, h8X, hrσ, hσN⟩

/-! ### B0–B8 ⟹ U0 -/

theorem lemma_2_7_of_B {z r q : ℕ} {zs : Fin n → ℕ} {W σ N ζ X Y ξ : ℕ} {b c d : Fin n → ℕ}
    (hr : z.factorial + 6 < r) (hB : BConds z r q zs W σ N ζ X Y ξ b c d) :
    U0 z r q zs ∧ z < N ∧ 1 < Y ∧ 8 * N ^ z < X := by
  obtain ⟨B0, B1, B2, B3, B4, B5, B6, B7, B8⟩ := hB
  have hzf : z ≤ z.factorial := Nat.self_le_factorial z
  have hrW : r ≤ W := by rw [B1]; omega
  have hqW : q ≤ W := by rw [B1]; omega
  have hziW : ∀ i, zs i ≤ W := fun i => by
    have := Finset.single_le_sum (f := zs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [B1]; omega
  have hbiW : ∀ i, b i ≤ W := fun i => by
    have := Finset.single_le_sum (f := b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [B1]; omega
  obtain ⟨x, hx⟩ := B2
  have hσ : W - 1 + W ^ (W - 2) ≤ σ := JSWW1976.lemma_2_3 (by omega) hx
  obtain ⟨x', hx'⟩ := B5
  have hσ7 : 7 ≤ σ := by
    have : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
    omega
  have hζ : N - 1 + N ^ (N - 2) ≤ ζ := JSWW1976.lemma_2_3 (by rw [B3]; nlinarith) hx'
  have bd := bounds hr hrW hσ B3 hζ
  have hfW : z.factorial ≤ W := by omega
  -- (9)
  have hq : z.factorial * q < W ^ (W - 2) := by
    calc z.factorial * q ≤ W * W := Nat.mul_le_mul hfW hqW
      _ = W ^ 2 := by ring
      _ < _ := bd.W2
  have hCr : z.factorial * r.choose z < W ^ (W - 2) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    calc r.descFactorial z ≤ r ^ z := Nat.descFactorial_le_pow r z
      _ ≤ W ^ z := Nat.pow_le_pow_left hrW z
      _ < _ := bd.Wz
  have hqb : ∀ i, z.factorial * (q * b i) < W ^ (W - 2) := fun i => by
    calc z.factorial * (q * b i) ≤ W * (W * W) :=
          Nat.mul_le_mul hfW (Nat.mul_le_mul hqW (hbiW i))
      _ = W ^ 3 := by ring
      _ < _ := bd.W3
  have hCz : ∀ i, z.factorial * (zs i).choose z < W ^ (W - 2) := fun i => by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    calc (zs i).descFactorial z ≤ (zs i) ^ z := Nat.descFactorial_le_pow _ z
      _ ≤ W ^ z := Nat.pow_le_pow_left (hziW i) z
      _ < _ := bd.Wz
  -- (10)
  have hrσ := bd.rσ
  have hσN := bd.σN
  have h10q : z.factorial * q < N - r := by omega
  have h10Cr : z.factorial * r.choose z < N - r := by omega
  have h10qb : ∀ i, z.factorial * (q * b i) < σ + d i := fun i => by have := hqb i; omega
  have h10Cz : ∀ i, z.factorial * (zs i).choose z < σ + d i := fun i => by have := hCz i; omega
  -- `8 N^z < X`
  have hζX : ζ ≤ X := by
    rw [B6]
    have h1 : 1 ≤ N - r := by omega
    have h2 : 1 ≤ ∏ i, (σ + d i) :=
      Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => by omega))
    calc ζ = ζ * 1 * 1 := by ring
      _ ≤ ζ * (N - r) * ∏ i, (σ + d i) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have h8X : 8 * N ^ z < X := by have := bd.eightN; have := bd.ζ_ge; omega
  have hzN : z < N := by have := bd.zN3; omega
  -- (11)
  have h11 : Y ≡ N.choose z [MOD X] := by rw [B0]; exact lemma_2_6 hzN (by omega)
  -- `q = C(r, z)`
  have hNrdvd : N - r ∣ X := by rw [B6]; exact ⟨ζ * ∏ i, (σ + d i), by ring⟩
  have hNrpos : 0 < N - r := by omega
  have hYq : Y ≡ q [MOD N - r] := by
    rw [B7]
    show (q + (ξ + 1) * (N - r)) % (N - r) = q % (N - r)
    rw [mul_comm, Nat.add_mul_mod_self_left]
  have hNr : N ≡ r [MOD N - r] := ((Nat.modEq_iff_dvd' (by omega)).2 (dvd_refl _)).symm
  have hCN : N.choose z ≡ r.choose z [MOD (N - r) / Nat.gcd (N - r) z.factorial] :=
    lemma_2_5 hNrpos hNr z
  have hgdvd : (N - r) / Nat.gcd (N - r) z.factorial ∣ N - r :=
    Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hqC : q ≡ r.choose z [MOD (N - r) / Nat.gcd (N - r) z.factorial] :=
    (Nat.ModEq.of_dvd hgdvd (hYq.symm.trans (Nat.ModEq.of_dvd hNrdvd h11))).trans hCN
  have hqeq : q = r.choose z := eq_of_modEq_div_gcd hNrpos hqC h10q h10Cr
  -- `q bᵢ = C(zᵢ, z)`
  have hqbC : ∀ i, q * b i = (zs i).choose z := by
    intro i
    have hdpos : 0 < σ + d i := by omega
    have hddvd : σ + d i ∣ X := by
      rw [B6]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => σ + d i) (Finset.mem_univ i)) _
    have hYqb : Y ≡ q * b i [MOD σ + d i] := by
      rw [B8 i]
      show (q * b i + c i * (σ + d i)) % (σ + d i) = (q * b i) % (σ + d i)
      rw [mul_comm (c i), Nat.add_mul_mod_self_left]
    have hCz' : N.choose z ≡ (zs i).choose z [MOD (σ + d i) / Nat.gcd (σ + d i) z.factorial] :=
      lemma_2_5 hdpos (B4 i) z
    have hgdvd' : (σ + d i) / Nat.gcd (σ + d i) z.factorial ∣ σ + d i :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    have h := (Nat.ModEq.of_dvd hgdvd' (hYqb.symm.trans (Nat.ModEq.of_dvd hddvd h11))).trans hCz'
    exact eq_of_modEq_div_gcd hdpos h (h10qb i) (h10Cz i)
  refine ⟨⟨hqeq, fun i => ⟨b i, (hqbC i).symm⟩⟩, hzN, ?_, h8X⟩
  -- `1 < Y`
  have hXY : X ≤ Y := by
    rw [B0]
    calc X ≤ X ^ (N - z) := Nat.le_self_pow (by omega) X
      _ ≤ (X + 1) ^ N / X ^ z := pow_le_partial_binomial hzN.le (by omega)
  omega

/-! ### U0 ⟹ B0–B8 -/

theorem exists_B_of_U0 {z r q : ℕ} {zs : Fin n → ℕ} (hr : z.factorial + 6 < r)
    (hdvd : z.factorial ∣ r + 1) (hU : U0 z r q zs) :
    ∃ (W σ N ζ X Y ξ : ℕ) (b c d : Fin n → ℕ), BConds z r q zs W σ N ζ X Y ξ b c d := by
  obtain ⟨hq, hdiv⟩ := hU
  have hzf : z ≤ z.factorial := Nat.self_le_factorial z
  have hf1 : 1 ≤ z.factorial := Nat.factorial_pos z
  have hqpos : 0 < q := by rw [hq]; exact Nat.choose_pos (by omega)
  -- bᵢ
  obtain ⟨b, hqb⟩ : ∃ b : Fin n → ℕ, ∀ i, q * b i = (zs i).choose z :=
    ⟨fun i => (zs i).choose z / q, fun i => Nat.mul_div_cancel' (hdiv i)⟩
  -- W, σ
  set W := r + q + ∑ i, zs i + ∑ i, b i with hW
  have hrW : r ≤ W := by omega
  have hziW : ∀ i, zs i ≤ W := fun i => by
    have := Finset.single_le_sum (f := zs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨σ, x, hx, -⟩ := JSWW1976.lemma_2_3_converse (e := W) (t := 1) (by omega) le_rfl
  have hσ : W - 1 + W ^ (W - 2) ≤ σ := JSWW1976.lemma_2_3 (by omega) hx
  have hσ7 : 7 ≤ σ := by
    have : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
    omega
  -- N, ζ
  set N := σ * (r + 1) with hN
  have hN2 : 2 ≤ N := by rw [hN]; nlinarith
  obtain ⟨ζ, x', hx', -⟩ := JSWW1976.lemma_2_3_converse (e := N) (t := 1) (by omega) le_rfl
  have hζ : N - 1 + N ^ (N - 2) ≤ ζ := JSWW1976.lemma_2_3 hN2 hx'
  have bd := bounds hr hrW hσ hN hζ
  have hrσ := bd.rσ
  have hσN := bd.σN
  have hzN : z < N := by have := bd.zN3; omega
  -- (9)-type bounds
  have hziσ : ∀ i, zs i < σ := fun i => by
    have := hziW i; have := bd.W8
    have : W ≤ W ^ (W - 2) := Nat.le_self_pow (by omega) W
    omega
  have hCz : ∀ i, z.factorial * (zs i).choose z < W ^ (W - 2) := fun i => by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    calc (zs i).descFactorial z ≤ (zs i) ^ z := Nat.descFactorial_le_pow _ z
      _ ≤ W ^ z := Nat.pow_le_pow_left (hziW i) z
      _ < _ := bd.Wz
  -- dᵢ: `σ + dᵢ = (N − zᵢ)/gcd(N − zᵢ, z!)`
  have hd : ∀ i, ∃ di, σ + di = (N - zs i) / Nat.gcd (N - zs i) z.factorial := by
    intro i
    set g := Nat.gcd (N - zs i) z.factorial with hg
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.factorial_pos z)
    have hgf : g ≤ z.factorial := Nat.le_of_dvd (Nat.factorial_pos z) (Nat.gcd_dvd_right _ _)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_left (N - zs i) z.factorial
    rw [← hg] at hm
    have hdm : (N - zs i) / g = m := by rw [hm, Nat.mul_div_cancel_left _ hgpos]
    refine ⟨m - σ, ?_⟩
    rw [hdm]
    -- σ g < N − zᵢ = g m, hence σ < m
    have hσg : σ * g < g * m := by
      have h1 : σ * g ≤ σ * z.factorial := Nat.mul_le_mul_left _ hgf
      have h2 : σ * z.factorial < σ * r := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      have h3 : σ * r < N - zs i := by
        have := hziσ i
        have : N = σ * r + σ := by rw [hN]; ring
        omega
      omega
    rw [mul_comm g] at hσg
    have : σ < m := lt_of_mul_lt_mul_right hσg (Nat.zero_le _)
    omega
  choose d hd using hd
  have hdpos : ∀ i, 0 < σ + d i := fun i => by omega
  have hB4 : ∀ i, N ≡ zs i [MOD σ + d i] := by
    intro i
    rw [hd i]
    have : (N - zs i) / Nat.gcd (N - zs i) z.factorial ∣ N - zs i :=
      Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    exact ((Nat.modEq_iff_dvd' (by have := hziσ i; have := bd.σN; omega)).2 this).symm
  -- X, Y
  set X := ζ * (N - r) * ∏ i, (σ + d i) with hX
  have hζX : ζ ≤ X := by
    have h1 : 1 ≤ N - r := by omega
    have h2 : 1 ≤ ∏ i, (σ + d i) :=
      Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 (fun i _ => by omega))
    calc ζ = ζ * 1 * 1 := by ring
      _ ≤ ζ * (N - r) * ∏ i, (σ + d i) := Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have h8X : 8 * N ^ z < X := by have := bd.eightN; have := bd.ζ_ge; omega
  have hXpos : 0 < X := by omega
  set Y := (X + 1) ^ N / X ^ z with hY
  have h11 : Y ≡ N.choose z [MOD X] := lemma_2_6 hzN (by omega)
  have hXY : X ≤ Y := by
    calc X ≤ X ^ (N - z) := Nat.le_self_pow (by omega) X
      _ ≤ (X + 1) ^ N / X ^ z := pow_le_partial_binomial hzN.le hXpos
  have hNY : N ≤ Y := by have := bd.ζ_ge; have := Nat.le_self_pow (show N - 2 ≠ 0 by omega) N; omega
  -- B7
  have hNrdvd : N - r ∣ X := ⟨ζ * ∏ i, (σ + d i), by rw [hX]; ring⟩
  have hNrpos : 0 < N - r := by omega
  have hcop : Nat.gcd (N - r) z.factorial = 1 := by
    have hzN' : z.factorial ∣ N := hdvd.trans ⟨σ, by rw [hN]; ring⟩
    have hg1 : Nat.gcd (N - r) z.factorial ∣ N := (Nat.gcd_dvd_right _ _).trans hzN'
    have hg2 : Nat.gcd (N - r) z.factorial ∣ N + 1 := by
      have h1 : Nat.gcd (N - r) z.factorial ∣ r + 1 := (Nat.gcd_dvd_right _ _).trans hdvd
      have h2 : Nat.gcd (N - r) z.factorial ∣ N - r := Nat.gcd_dvd_left _ _
      have := Nat.dvd_add h2 h1
      rwa [show N - r + (r + 1) = N + 1 by omega] at this
    have := Nat.dvd_sub hg2 hg1
    rw [Nat.add_sub_cancel_left] at this
    exact Nat.dvd_one.1 this
  have hNr : N ≡ r [MOD N - r] := ((Nat.modEq_iff_dvd' (by omega)).2 (dvd_refl _)).symm
  have hCN : N.choose z ≡ r.choose z [MOD N - r] := by
    have := lemma_2_5 hNrpos hNr z
    rwa [hcop, Nat.div_one] at this
  have hYq : Y ≡ q [MOD N - r] := by
    rw [hq]; exact (Nat.ModEq.of_dvd hNrdvd h11).trans hCN
  have hqY : q < Y := by
    have h1 : q ≤ r ^ z := by rw [hq]; exact Nat.choose_le_pow r z
    have h2 : r ^ z ≤ N ^ (N - 3) := by
      calc r ^ z ≤ N ^ z := Nat.pow_le_pow_left (by omega) z
        _ ≤ N ^ (N - 3) := Nat.pow_le_pow_right (by omega) (by have := bd.zN3; omega)
    have h3 : N ^ (N - 3) < N ^ (N - 2) := Nat.pow_lt_pow_right (by have := bd.N9; omega) (by have := bd.N9; omega)
    have := bd.ζ_ge
    omega
  obtain ⟨k, hk⟩ : N - r ∣ Y - q := (Nat.modEq_iff_dvd' hqY.le).1 hYq.symm
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  -- B8
  have hc : ∀ i, ∃ ci, Y = q * b i + ci * (σ + d i) := by
    intro i
    have hddvd : σ + d i ∣ X := by
      rw [hX]
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun i => σ + d i) (Finset.mem_univ i)) _
    have hNz : 0 < N - zs i := by have := hziσ i; omega
    have hCz' : N.choose z ≡ (zs i).choose z [MOD σ + d i] := by
      rw [hd i]
      exact lemma_2_5 hNz ((Nat.modEq_iff_dvd' (by have := hziσ i; omega)).2 (dvd_refl _)).symm z
    have hYqb : Y ≡ q * b i [MOD σ + d i] := by
      rw [hqb i]; exact (Nat.ModEq.of_dvd hddvd h11).trans hCz'
    have hle : q * b i ≤ Y := by
      rw [hqb i]
      have h1 := hCz i
      have h2 : (zs i).choose z ≤ z.factorial * (zs i).choose z := Nat.le_mul_of_pos_left _ hf1
      have h3 := bd.σN
      have h4 := hNY
      omega
    obtain ⟨ci, hci⟩ := (Nat.modEq_iff_dvd' hle).1 hYqb.symm
    exact ⟨ci, by rw [mul_comm (σ + d i)] at hci; omega⟩
  choose c hc using hc
  refine ⟨W, σ, N, ζ, X, Y, k - 1, b, c, d, ⟨rfl, rfl, ⟨x, hx⟩, rfl, hB4, ⟨x', hx'⟩, rfl, ?_, hc⟩⟩
  rw [show k - 1 + 1 = k by omega, mul_comm]
  omega

/-- **Lemma 2.7.** -/
theorem lemma_2_7 {z r q : ℕ} {zs : Fin n → ℕ} (hr : z.factorial + 6 < r)
    (hdvd : z.factorial ∣ r + 1) :
    U0 z r q zs ↔ ∃ (W σ N ζ X Y ξ : ℕ) (b c d : Fin n → ℕ), BConds z r q zs W σ N ζ X Y ξ b c d :=
  ⟨exists_B_of_U0 hr hdvd, fun ⟨_, _, _, _, _, _, _, _, _, _, h⟩ => (lemma_2_7_of_B hr h).1⟩

end Jones1978
