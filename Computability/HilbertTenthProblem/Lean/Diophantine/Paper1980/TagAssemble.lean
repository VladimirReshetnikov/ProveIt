import Diophantine.Paper1980.TagDecode91
import Diophantine.Paper1980.RowSum

/-!
# Assembling a solution of the 91-operation tag certificate

The converse direction (`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`, §5, and
`EXPLORATION_ZERO_TERMINAL_TAG_PARITY.md`, §4): given positive outer coordinates
satisfying the eight outer equations, with the nine conceptual fields Boolean and below
`q = 3^e`, the first field of unit digit `1`, and the packed word of even parity, the
packed index `r = P + rep(9e)` has the unit-two mask (so `q⁹ ∣ C(2r, r)`), lies in
`(q⁹/2, q⁹)`, and the positive kernel converse supplies the sixteen Pell witnesses.
-/

namespace Jones1980

open Ternary

namespace Ternary

/-- Adding the repunit to a Boolean word below `3^N`: no carries, every digit grows by one. -/
theorem dg_add_rep {P N : ℕ} (hP : Bool3 P) (hPlt : P < 3 ^ N) (p : ℕ) (hp : p < N) :
    dg (P + rep N) p = dg P p + 1 := by
  rw [dg_add_of_le_two (fun p => by have := hP p; have := bool3_rep N p; omega), dg_rep, if_pos hp]

end Ternary

/-- The positive converse assembly: outer coordinates satisfying the eight outer equations,
Boolean fields below `q`, unit digit `1`, even packed word ⟹ `Solvable91`. -/
theorem assemble91 {T : Tag91} {Ninit Linit : ℕ} {Q S1 Tc E H R L q v D Z e : ℕ}
    (hq : q = 3 ^ e) (he : 1 ≤ e)
    (hQ : 0 < Q) (hS1 : 0 < S1) (hTc : 0 < Tc) (hE : 0 < E) (hH : 0 < H) (hR : 0 < R)
    (hL : 0 < L) (hv : 0 < v) (hD : 0 < D) (hZ : 0 < Z)
    (E0 : T.Khalf * D = R)
    (E1 : (D : ℤ) * ((Tc : ℤ) - E + T.Uthird * (2 * Q + S1)) = T.N Q S1 Tc - Ninit)
    (E2 : (D : ℤ) * ((L : ℤ) + ((T.B : ℤ) - 1) * (2 * Q + S1)) = (L : ℤ) - Linit + 3 * q)
    (E3 : R * H + 1 = H + q) (E4 : R * H = T.C * Z) (E5 : R * v = q)
    (hS1H : S1 ≤ H) (hM1L : 2 * Q + S1 ≤ L) (hEcc : E ≤ T.cc * H)
    {GN : ℕ} (hGN : (GN : ℤ) = T.N Q S1 Tc + T.jg * Z)
    (b0 : Bool3 (H - S1)) (b1 : Bool3 S1) (b2 : Bool3 Q) (b3 : Bool3 (Q + Z))
    (b4 : Bool3 (L - (2 * Q + S1))) (b5 : Bool3 (2 * Q + S1)) (b6 : Bool3 (T.cc * H - E))
    (b7 : Bool3 E) (b8 : Bool3 GN)
    (l0 : H - S1 < q) (l1 : S1 < q) (l2 : Q < q) (l3 : Q + Z < q) (l4 : L - (2 * Q + S1) < q)
    (l5 : 2 * Q + S1 < q) (l6 : T.cc * H - E < q) (l7 : E < q) (l8 : GN < q)
    (hunit : (H - S1) % 3 = 1)
    (hpar : 2 ∣ (H - S1) + q * (S1 + q * (Q + q * ((Q + Z) + q * ((L - (2 * Q + S1)) +
      q * ((2 * Q + S1) + q * ((T.cc * H - E) + q * (E + q * GN))))))) + rep (9 * e)) :
    Solvable91 T Ninit Linit := by
  -- the packed word
  obtain ⟨P, hPdef⟩ : ∃ P, P = (H - S1) + q * (S1 + q * (Q + q * ((Q + Z) + q * ((L - (2 * Q + S1)) +
    q * ((2 * Q + S1) + q * ((T.cc * H - E) + q * (E + q * GN))))))) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; positivity
  -- Booleanity and size of the packed word
  have hPb : Bool3 P := by
    rw [hPdef, hq]
    refine bool3_chunk_cons b0 (hq ▸ l0) ?_
    refine bool3_chunk_cons b1 (hq ▸ l1) ?_
    refine bool3_chunk_cons b2 (hq ▸ l2) ?_
    refine bool3_chunk_cons b3 (hq ▸ l3) ?_
    refine bool3_chunk_cons b4 (hq ▸ l4) ?_
    refine bool3_chunk_cons b5 (hq ▸ l5) ?_
    refine bool3_chunk_cons b6 (hq ▸ l6) ?_
    exact bool3_chunk_cons b7 (hq ▸ l7) b8
  have hPlt : P < 3 ^ (9 * e) := by
    rw [hPdef, hq]
    have h8 : GN < 3 ^ (1 * e) := by rw [one_mul, ← hq]; exact l8
    have h7 := chunk_cons_lt (hq ▸ l7) h8
    have h6 := chunk_cons_lt (hq ▸ l6) h7
    have h5 := chunk_cons_lt (hq ▸ l5) h6
    have h4 := chunk_cons_lt (hq ▸ l4) h5
    have h3 := chunk_cons_lt (hq ▸ l3) h4
    have h2 := chunk_cons_lt (hq ▸ l2) h3
    have h1 := chunk_cons_lt (hq ▸ l1) h2
    have h0 := chunk_cons_lt (hq ▸ l0) h1
    simpa using h0
  have hPrep : P ≤ rep (9 * e) := hPb.le_rep hPlt
  -- the index
  obtain ⟨r, hrdef⟩ : ∃ r, r = P + rep (9 * e) := ⟨_, rfl⟩
  have hrep9 : 2 * rep (9 * e) + 1 = 3 ^ (9 * e) := two_mul_rep_add_one _
  have hq9 : q ^ 9 = 3 ^ (9 * e) := by rw [hq, ← pow_mul, mul_comm]
  have hrlt : r < 3 ^ (9 * e) := by omega
  have hrP : P ≤ r := by omega
  have h39 : (19683 : ℕ) ≤ 3 ^ (9 * e) := by
    calc (19683 : ℕ) = 3 ^ 9 := by norm_num
      _ ≤ 3 ^ (9 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr27 : 27 ≤ r := by omega
  have hr2 : 2 ≤ r := by omega
  have hβ : 0 < 3 ^ (9 * e) - r := by omega
  -- the mask of `r`
  have h3q : ∃ q', q = 3 * q' := by
    obtain ⟨q', hq'⟩ : (3 : ℕ) ∣ q := by rw [hq]; exact dvd_pow_self 3 (by omega)
    exact ⟨q', hq'⟩
  have hP0 : P % 3 = 1 := by
    obtain ⟨q', hq'⟩ := h3q
    rw [hPdef, hq']
    rw [show 3 * q' * (S1 + 3 * q' * (Q + 3 * q' * (Q + Z + 3 * q' * (L - (2 * Q + S1) +
        3 * q' * (2 * Q + S1 + 3 * q' * (T.cc * H - E + 3 * q' * (E + 3 * q' * GN))))))) =
      3 * (q' * (S1 + 3 * q' * (Q + 3 * q' * (Q + Z + 3 * q' * (L - (2 * Q + S1) +
        3 * q' * (2 * Q + S1 + 3 * q' * (T.cc * H - E + 3 * q' * (E + 3 * q' * GN)))))))) by ring,
      Nat.add_mul_mod_self_left]
    exact hunit
  have hr0 : r % 3 = 2 := by
    have := dg_add_rep hPb hPlt 0 (by omega)
    rw [dg_zero_pos, dg_zero_pos] at this
    rw [hrdef]
    omega
  have hrd : ∀ i, 1 ≤ i → i < 9 * e → r / 3 ^ i % 3 ≠ 0 := by
    intro i _ hi
    have := dg_add_rep hPb hPlt i hi
    unfold dg at this
    rw [hrdef]
    omega
  have hcentral : 3 ^ (9 * e) ∣ (2 * r).choose r := (ternary_mask (by omega) hrlt).2 ⟨hr0, hrd⟩
  -- the kernel witnesses at `r`
  have hreven : 2 ∣ r := by rw [hrdef, hPdef]; exact hpar
  have hD₀r : 3 ^ (9 * e) < r ^ 2 := by
    have h1 : 3 ^ (9 * e) ≤ 3 * r := by omega
    have h2 : 4 * r ≤ r * r := Nat.mul_le_mul (show 4 ≤ r by omega) (le_refl r)
    have h3 : r * r = r ^ 2 := (sq r).symm
    omega
  obtain ⟨a, c, d, f, h, i, j, k, o, s, w, τ, η, ζ, γ, y, hKP, hK⟩ :=
    kernel3_witnesses (D₀ := 3 ^ (9 * e)) rfl hr2 hreven hD₀r hcentral
  rw [← hq9] at hK
  -- the packed index equation
  have hcast : (P : ℤ) = ((H : ℤ) - S1) + q * (S1 + q * (Q + q * ((Q + Z) + q * (((L : ℤ) - (2 * Q + S1)) +
      q * ((2 * Q + S1) + q * (((T.cc * H : ℕ) : ℤ) - E + q * (E + q * (GN : ℤ)))))))) := by
    rw [hPdef]
    push_cast [Nat.cast_sub hS1H, Nat.cast_sub hM1L, Nat.cast_sub hEcc]
    ring
  have E6 : (2 * r + 1 : ℤ) = (q : ℤ) ^ 9 + 2 * ((H : ℤ) + ((q : ℤ) - 1) * S1 +
      (q : ℤ) ^ 2 * (Q + q * (Q + Z)) + (q : ℤ) ^ 4 * ((L : ℤ) + ((q : ℤ) - 1) * (2 * Q + S1) +
      (q : ℤ) ^ 2 * (T.cc * H + ((q : ℤ) - 1) * E + (q : ℤ) ^ 2 * (T.N Q S1 Tc + T.jg * Z)))) := by
    have hr' : (r : ℤ) = P + rep (9 * e) := by rw [hrdef]; push_cast; ring
    have hrep9Z : 2 * (rep (9 * e) : ℤ) + 1 = (q : ℤ) ^ 9 := by
      have h : ((2 * rep (9 * e) + 1 : ℕ) : ℤ) = ((q ^ 9 : ℕ) : ℤ) := by rw [hrep9, ← hq9]
      push_cast at h
      exact h
    rw [hr', hcast, ← hGN]
    push_cast
    linear_combination hrep9Z
  have E7 : r + (3 ^ (9 * e) - r) = q ^ 9 := by rw [hq9]; omega
  refine ⟨Q, S1, Tc, E, H, R, L, q, v, r, 3 ^ (9 * e) - r, a, c, d, f, h, i, j, k, o, s, w, τ, η,
    ζ, γ, y, D, Z, ⟨hQ, hS1, hTc, hE, hH, hR, hL, hq0, hv, by omega, hβ, hD, hZ, hKP⟩,
    ⟨E0, E1, E2, E3, E4, E5, E6, E7, hK⟩⟩

end Jones1980
