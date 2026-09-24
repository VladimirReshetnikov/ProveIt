import Diophantine.Paper1980.TagGeometry91

/-!
# The nine Boolean fields of the 91-operation tag certificate

`EXPLORATION_COMPILED_INITIAL_TAG_BOUND.md`, §2, and `EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`,
§§2–3.  The packed word `P = r − rep(9e)` is Boolean (`mask91`) and equals, by the
index equation, the base-`q` Horner word of the nine conceptual fields

    S₀ = H − S₁, S₁, Q, G = Q + Z, M₀ = L − M₁, M₁, Ē = cc·H − E, E, GN = N + jZ.

Scalar bounds obtained from the outer equations alone (`2H + 1 ≤ q`, `162 M₁ ≤ q`,
`80 L < q`, `729 Z < 2q`, `243 cc·H < q`, `2E < q`, `0 < GN ≤ rep e`) place every field
in `(−q/2, q)`, so the greedy chunk decoding (`chunk_step`) recovers each field as a
base-`q` chunk of `P`: nonnegative and Boolean.  The bound on `E` uses the content
identity `3RE = (R − K)N + R(UM₁ − S₁) + K·Ninit` and the input contract
(`Ninit < Linit`, `K² Linit < C`).
-/

namespace Jones1980

open Ternary

/-- The encoded-instance contract: `Linit = 3^ℓ` with `ℓ ≥ β`, `Ninit` a Boolean word below
`Linit`, and `K² Linit < C`. -/
structure Input91 (T : Tag91) (Ninit Linit : ℕ) : Prop where
  Linit_pow : ∃ ℓ β, 2 ≤ β ∧ T.Khalf = 3 ^ (β - 1) ∧ β ≤ ℓ ∧ Linit = 3 ^ ℓ
  Ninit_bool : Bool3 Ninit
  Ninit_lt : Ninit < Linit
  bound : (3 * T.Khalf) ^ 2 * Linit < T.C

/-- The decoded fields: nonnegativity of the complements and Booleanity of all nine. -/
structure Fields91 (T : Tag91) (Q S1 Tc E H L Z e : ℕ) : Prop where
  S1_le : S1 ≤ H
  M1_le : 2 * Q + S1 ≤ L
  E_le : E ≤ T.cc * H
  GN_pos : 0 < T.N Q S1 Tc + T.jg * Z
  GN_le : T.N Q S1 Tc + T.jg * Z ≤ (rep e : ℤ)
  bS0 : Bool3 (H - S1)
  bS1 : Bool3 S1
  bQ : Bool3 Q
  bG : Bool3 (Q + Z)
  bM0 : Bool3 (L - (2 * Q + S1))
  bM1 : Bool3 (2 * Q + S1)
  bEbar : Bool3 (T.cc * H - E)
  bE : Bool3 E
  bGN : ∀ GN : ℕ, (GN : ℤ) = T.N Q S1 Tc + T.jg * Z → Bool3 GN
  H_lt : 2 * H + 1 ≤ 3 ^ e
  L_lt : 80 * L < 3 ^ e
  Z_lt : 729 * Z < 2 * 3 ^ e
  ccH_lt : 243 * (T.cc * H) < 3 ^ e
  M1_lt : 162 * (2 * Q + S1) ≤ 3 ^ e
  E_lt : 2 * E < 3 ^ e

section Fields

variable {T : Tag91} {Ninit Linit : ℕ}
  {Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z : ℕ}
  (hT : T.Ok)
  (hP : Pos91 Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)
  (hS : Sys91 T Ninit Linit Q S1 Tc E H R L q v r β a c d f h i j k o s w τ η ζ γ y D Z)

include hT hP hS

/-- `D ≥ 27k² ≥ 243`. -/
theorem D_ge91 : 27 * T.Khalf ^ 2 ≤ D ∧ 243 ≤ D := by
  have hk := three_le_Khalf hT
  have h1 : (3 * T.Khalf) ^ 3 < R := lt_of_lt_of_le hT.C_gt_K3 (C_le_R91 hT hP hS)
  have h0 := hS.E0
  have h2 : (3 * T.Khalf) ^ 3 = T.Khalf * (27 * T.Khalf ^ 2) := by ring
  rw [h2, ← h0] at h1
  have h3 : 27 * T.Khalf ^ 2 < D := Nat.lt_of_mul_lt_mul_left h1
  have h4 : 9 ≤ T.Khalf ^ 2 := by nlinarith
  omega

/-- `2H + 1 ≤ q`. -/
theorem H_bound91 : 2 * H + 1 ≤ q := by
  have h3 := hS.E3
  have hR := R_ge91 hT hP hS
  have : 3 * H ≤ R * H := Nat.mul_le_mul_right _ hR
  omega

/-- `162 M₁ ≤ q`. -/
theorem M1_small91 : 162 * (2 * Q + S1) ≤ q := by
  have h1 := marker_bound91 hT hP hS
  have h2 := (D_ge91 hT hP hS).2
  have : 2 * 243 * (2 * Q + S1) ≤ 2 * D * (2 * Q + S1) := by
    apply Nat.mul_le_mul_right; omega
  omega

/-- The length transport in the form `D(B − 1)M₁ ≤ 3q` (as natural numbers). -/
theorem DBM_le91 : D * ((T.B - 1) * (2 * Q + S1)) ≤ 3 * q := by
  have h2 := hS.E2
  have hB := three_le_B hT
  have hD : (1 : ℤ) ≤ D := by exact_mod_cast hP.D
  have hL : (0 : ℤ) ≤ L := by positivity
  have hLi : (0 : ℤ) ≤ Linit := by positivity
  have h4 : (L : ℤ) ≤ D * L := by nlinarith
  have hcast : ((T.B - 1 : ℕ) : ℤ) = (T.B : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have : ((D * ((T.B - 1) * (2 * Q + S1)) : ℕ) : ℤ) ≤ 3 * q := by
    push_cast
    rw [hcast]
    nlinarith
  exact_mod_cast this

/-- `80 L < q`. -/
theorem L_small91 : 80 * L < q := by
  have h2 := hS.E2
  have hD := (D_ge91 hT hP hS).2
  have hDZ : (243 : ℤ) ≤ D := by exact_mod_cast hD
  have hB : (3 : ℤ) ≤ T.B := by exact_mod_cast three_le_B hT
  have hM : (0 : ℤ) ≤ 2 * Q + S1 := by positivity
  have hL : (0 : ℤ) ≤ L := by positivity
  have hLi : (0 : ℤ) ≤ Linit := by positivity
  have hDM : (0 : ℤ) ≤ D * (((T.B : ℤ) - 1) * (2 * Q + S1)) := by
    apply mul_nonneg (by positivity); exact mul_nonneg (by linarith) hM
  have h4 : (243 : ℤ) * L ≤ D * L := mul_le_mul_of_nonneg_right hDZ hL
  have h2' : (D : ℤ) * L + D * (((T.B : ℤ) - 1) * (2 * Q + S1)) = L - Linit + 3 * q := by
    linear_combination h2
  have hq1 : (1 : ℤ) ≤ q := by have := hP.q; exact_mod_cast this
  have : (80 * L : ℤ) < q := by linarith
  exact_mod_cast this

/-- `729 Z < 2q`. -/
theorem Z_small91 : 729 * Z < 2 * q := by
  have h3 := hS.E3
  have h4 := hS.E4
  have hC : 729 ≤ T.C := by
    have := hT.C_gt_K3
    have hk := three_le_Khalf hT
    have : 9 ^ 3 ≤ (3 * T.Khalf) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  have hH := hP.H
  have hHq := H_bound91 hT hP hS
  have h5 : 729 * Z ≤ T.C * Z := Nat.mul_le_mul_right _ hC
  omega

/-- `243 cc·H < q`. -/
theorem ccH_small91 : 243 * (T.cc * H) < q := by
  have h3 := hS.E3
  have h0 := hS.E0
  have hcc := hT.cc_eq
  have hD := (D_ge91 hT hP hS).2
  have hH := hP.H
  have hHq := H_bound91 hT hP hS
  have h1 : 243 * (T.Khalf * H) ≤ T.Khalf * D * H := by
    have : 243 * T.Khalf ≤ T.Khalf * D := by
      calc 243 * T.Khalf = T.Khalf * 243 := mul_comm _ _
        _ ≤ T.Khalf * D := Nat.mul_le_mul_left _ hD
    calc 243 * (T.Khalf * H) = (243 * T.Khalf) * H := by ring
      _ ≤ (T.Khalf * D) * H := Nat.mul_le_mul_right _ this
  rw [h0] at h1
  have h2 : 2 * (T.cc * H) < T.Khalf * H := by
    have : (2 * T.cc) * H < T.Khalf * H := Nat.mul_lt_mul_of_pos_right (by omega) hH
    calc 2 * (T.cc * H) = (2 * T.cc) * H := by ring
      _ < T.Khalf * H := this
  omega

/-- The content identity `3RE = (R − K)N + R(UM₁ − S₁) + K·Ninit`. -/
theorem content_identity91 :
    (3 * (R : ℤ) * E : ℤ) = ((R : ℤ) - 3 * T.Khalf) * T.N Q S1 Tc +
      R * ((3 * T.Uthird + T.ε) * (2 * Q + S1) - S1) + 3 * T.Khalf * Ninit := by
  have h1 := hS.E1
  have hRkD : (R : ℤ) = T.Khalf * D := by exact_mod_cast hS.E0.symm
  have hε := hT.ε_lt
  rw [hRkD]
  unfold Tag91.N at h1 ⊢
  rcases (by omega : T.ε = 0 ∨ T.ε = 1) with h0 | h0
  · simp only [h0, if_true] at h1 ⊢
    push_cast
    linear_combination (-(3 * (T.Khalf : ℤ))) * h1
  · simp only [h0, one_ne_zero, if_false] at h1 ⊢
    push_cast
    linear_combination (-(3 * (T.Khalf : ℤ))) * h1

/-- `GN ≤ rep e` from the Boolean packed word (all other terms of the factored packing
are nonnegative). -/
theorem GN_le_rep91 {e : ℕ} (hq : q = 3 ^ e) (hrep : rep (9 * e) ≤ r)
    (hP2 : 2 * (r - rep (9 * e)) + q ^ 9 = 2 * r + 1)
    (hPb : Bool3 (r - rep (9 * e))) :
    T.N Q S1 Tc + T.jg * Z ≤ (rep e : ℤ) := by
  have h6 := hS.E6
  have hPZ : (2 * ((r - rep (9 * e) : ℕ) : ℤ) + (q : ℤ) ^ 9 : ℤ) = 2 * r + 1 := by
    have hcast : ((2 * (r - rep (9 * e)) + q ^ 9 : ℕ) : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by
      rw [hP2]
    push_cast at hcast
    exact hcast
  have hPle : r - rep (9 * e) ≤ rep (9 * e) := by
    have : r - rep (9 * e) < 3 ^ (9 * e) := by
      have hr := r_lt91 hP hS
      rw [hq, ← pow_mul, mul_comm e 9] at hr; omega
    exact hPb.le_rep this
  have hrep9 : 2 * rep (9 * e) + 1 = 3 ^ (9 * e) := two_mul_rep_add_one _
  have hrepe : 2 * rep e + 1 = 3 ^ e := two_mul_rep_add_one e
  have hGN := GN_pos91 hT hP hS
  -- the packed word dominates `q⁸ GN`
  have hq1 : (1 : ℤ) ≤ q := by have := hP.q; exact_mod_cast this
  have hH : (0 : ℤ) ≤ H := by positivity
  have hS1 : (0 : ℤ) ≤ S1 := by positivity
  have hQ : (0 : ℤ) ≤ Q := by positivity
  have hZ : (0 : ℤ) ≤ Z := by positivity
  have hL : (0 : ℤ) ≤ L := by positivity
  have hE : (0 : ℤ) ≤ E := by positivity
  have hcc : (0 : ℤ) ≤ T.cc := by positivity
  have hq1' : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
  have t1 : (0 : ℤ) ≤ ((q : ℤ) - 1) * S1 := mul_nonneg hq1' hS1
  have t2 : (0 : ℤ) ≤ (q : ℤ) ^ 2 * (Q + q * (Q + Z)) := by positivity
  have t3 : (0 : ℤ) ≤ ((q : ℤ) - 1) * (2 * Q + S1) := mul_nonneg hq1' (by positivity)
  have t4 : (0 : ℤ) ≤ ((q : ℤ) - 1) * E := mul_nonneg hq1' hE
  have t6 : (0 : ℤ) ≤ (q : ℤ) ^ 4 * ((L : ℤ) + ((q : ℤ) - 1) * (2 * Q + S1) +
      (q : ℤ) ^ 2 * (T.cc * H + ((q : ℤ) - 1) * E)) := by positivity
  have hdom : (q : ℤ) ^ 8 * (T.N Q S1 Tc + T.jg * Z) ≤ ((r - rep (9 * e) : ℕ) : ℤ) := by
    linarith
  -- so `2 q⁸ GN ≤ q⁹ − 1 < q⁹`, hence `2 GN < q`
  have hPleZ : ((r - rep (9 * e) : ℕ) : ℤ) ≤ (rep (9 * e) : ℤ) := by exact_mod_cast hPle
  have hq9 : (2 * (rep (9 * e) : ℤ) + 1) = (q : ℤ) ^ 9 := by
    rw [hq]; push_cast; rw [← pow_mul, mul_comm e 9]; exact_mod_cast hrep9
  have hq8 : (0 : ℤ) < (q : ℤ) ^ 8 := by positivity
  have h2 : (q : ℤ) ^ 8 * (2 * (T.N Q S1 Tc + T.jg * Z)) < (q : ℤ) ^ 8 * q := by
    have : (q : ℤ) ^ 8 * q = (q : ℤ) ^ 9 := by ring
    rw [this]; linarith
  have h3 : 2 * (T.N Q S1 Tc + T.jg * Z) < (q : ℤ) := lt_of_mul_lt_mul_left h2 hq8.le
  have hrepZ : 2 * (rep e : ℤ) + 1 = q := by rw [hq]; exact_mod_cast hrepe
  omega

/-- `2 U D M₁ < 27 q`. -/
theorem UDM_small91 (hU : 3 * T.Uthird + T.ε < 3 * T.B) :
    2 * ((3 * T.Uthird + T.ε) * (D * (2 * Q + S1))) < 27 * q := by
  have hDBM := DBM_le91 hT hP hS
  have hB := three_le_B hT
  have hq := hP.q
  set X := (3 * T.Uthird + T.ε) * (D * (2 * Q + S1)) with hX
  have h1 : 2 * T.B ≤ 3 * (T.B - 1) := by omega
  have h2 : (3 * (T.B - 1)) * X = 3 * (3 * T.Uthird + T.ε) * (D * ((T.B - 1) * (2 * Q + S1))) := by
    rw [hX]; ring
  have h3 : 3 * (3 * T.Uthird + T.ε) * (D * ((T.B - 1) * (2 * Q + S1))) ≤
      3 * (3 * T.Uthird + T.ε) * (3 * q) := Nat.mul_le_mul_left _ hDBM
  have h4 : 3 * (3 * T.Uthird + T.ε) * (3 * q) < 3 * (3 * T.B) * (3 * q) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h5 : 2 * X * T.B < 27 * q * T.B := by
    calc 2 * X * T.B = (2 * T.B) * X := by ring
      _ ≤ (3 * (T.B - 1)) * X := Nat.mul_le_mul_right _ h1
      _ = 3 * (3 * T.Uthird + T.ε) * (D * ((T.B - 1) * (2 * Q + S1))) := h2
      _ ≤ 3 * (3 * T.Uthird + T.ε) * (3 * q) := h3
      _ < 3 * (3 * T.B) * (3 * q) := h4
      _ = 27 * q * T.B := by ring
  exact Nat.lt_of_mul_lt_mul_right h5

/-- `2E < q`, from the content identity and the input contract. -/
theorem E_small91 (hU : 3 * T.Uthird + T.ε < 3 * T.B) (hI : Input91 T Ninit Linit) {e : ℕ}
    (hq : q = 3 ^ e) (hGNle : T.N Q S1 Tc + T.jg * Z ≤ (rep e : ℤ)) : 2 * E < q := by
  have hid := content_identity91 hT hP hS
  have hk := three_le_Khalf hT
  have hR0 := hP.R
  have hq3 := q_ge91 hT hP hS
  have hrepe : 2 * rep e + 1 = q := by rw [hq]; exact two_mul_rep_add_one e
  -- `N ≤ GN ≤ rep e`
  have hN : T.N Q S1 Tc ≤ (rep e : ℤ) := by
    have : (0 : ℤ) ≤ T.jg * Z := by positivity
    linarith
  -- `27 k ≤ R`
  have hKR : 27 * T.Khalf ≤ R := by
    have h1 : (3 * T.Khalf) ^ 3 < R := lt_of_lt_of_le hT.C_gt_K3 (C_le_R91 hT hP hS)
    have h2 : 27 * T.Khalf ≤ (3 * T.Khalf) ^ 3 := by
      have : T.Khalf ≤ T.Khalf ^ 3 := Nat.le_self_pow (by norm_num) _
      calc 27 * T.Khalf ≤ 27 * T.Khalf ^ 3 := Nat.mul_le_mul_left _ this
        _ = (3 * T.Khalf) ^ 3 := by ring
    omega
  -- `2 R U M₁ < 27 k q`
  have hUM : 2 * (R * ((3 * T.Uthird + T.ε) * (2 * Q + S1))) < 27 * T.Khalf * q := by
    have h0 := hS.E0
    have h7 := UDM_small91 hT hP hS hU
    calc 2 * (R * ((3 * T.Uthird + T.ε) * (2 * Q + S1)))
        = T.Khalf * (2 * ((3 * T.Uthird + T.ε) * (D * (2 * Q + S1)))) := by rw [← h0]; ring
      _ < T.Khalf * (27 * q) := Nat.mul_lt_mul_of_pos_left h7 (by omega)
      _ = 27 * T.Khalf * q := by ring
  -- `K Ninit < R`
  have hKNi : 3 * T.Khalf * Ninit < R := by
    have h1 : 3 * T.Khalf * Ninit < 3 * T.Khalf * Linit :=
      Nat.mul_lt_mul_of_pos_left hI.Ninit_lt (by omega)
    have h2 : 3 * T.Khalf * Linit ≤ (3 * T.Khalf) ^ 2 * Linit := by
      apply Nat.mul_le_mul_right
      calc 3 * T.Khalf = (3 * T.Khalf) ^ 1 := (pow_one _).symm
        _ ≤ (3 * T.Khalf) ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h3 := hI.bound
    have h4 := C_le_R91 hT hP hS
    omega
  -- assemble over the integers
  have hidZ : 3 * ((R : ℤ) * E) = R * T.N Q S1 Tc - 3 * T.Khalf * T.N Q S1 Tc +
      R * ((3 * T.Uthird + T.ε) * (2 * Q + S1)) - R * S1 + 3 * T.Khalf * Ninit := by
    linear_combination hid
  have hRKZ : (3 * T.Khalf : ℤ) ≤ R := by
    have : 3 * T.Khalf ≤ R := by omega
    exact_mod_cast this
  have hRKN : ((R : ℤ) - 3 * T.Khalf) * T.N Q S1 Tc ≤ ((R : ℤ) - 3 * T.Khalf) * rep e :=
    mul_le_mul_of_nonneg_left hN (by linarith)
  have hRKN' : (R : ℤ) * T.N Q S1 Tc - 3 * T.Khalf * T.N Q S1 Tc ≤
      R * rep e - 3 * T.Khalf * rep e := by linear_combination hRKN
  have hUMZ : 2 * ((R : ℤ) * ((3 * T.Uthird + T.ε) * (2 * Q + S1))) < 27 * T.Khalf * q := by
    exact_mod_cast hUM
  have hKNiZ : 3 * (T.Khalf : ℤ) * Ninit < R := by exact_mod_cast hKNi
  have hRS1 : (0 : ℤ) ≤ (R : ℤ) * S1 := by positivity
  have hrepZ : 2 * (rep e : ℤ) + 1 = q := by exact_mod_cast hrepe
  have hRrep : 2 * ((R : ℤ) * rep e) + R = R * q := by
    have : (R : ℤ) * (2 * rep e + 1) = R * q := by rw [hrepZ]
    linear_combination this
  have hkrep : 2 * (3 * (T.Khalf : ℤ) * rep e) + 3 * T.Khalf = 3 * T.Khalf * q := by
    have : (3 * (T.Khalf : ℤ)) * (2 * rep e + 1) = 3 * T.Khalf * q := by rw [hrepZ]
    linear_combination this
  have hRq2 : 2 * (R : ℤ) ≤ R * q := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
    nlinarith
  have hkq : 27 * ((T.Khalf : ℤ) * q) ≤ R * q := by
    have h1 : (27 * T.Khalf : ℤ) ≤ R := by exact_mod_cast hKR
    have h2 : (0 : ℤ) ≤ q := by positivity
    nlinarith
  have hk0 : (0 : ℤ) ≤ T.Khalf := by positivity
  have h6 : 6 * ((R : ℤ) * E) < 3 * (R * q) := by
    nlinarith
  have hR3 : (0 : ℤ) < 3 * (R : ℤ) := by positivity
  have h7 : (3 * (R : ℤ)) * (2 * E) < (3 * (R : ℤ)) * q := by linarith
  have h8 : (2 * E : ℤ) < q := lt_of_mul_lt_mul_left h7 hR3.le
  exact_mod_cast h8

omit hT in
/-- The packed word `P = r − rep(9e)` is the Horner word of the nine fields. -/
theorem packed_eq91 {e : ℕ} (hq : q = 3 ^ e) (hP2 : 2 * (r - rep (9 * e)) + q ^ 9 = 2 * r + 1) :
    ((r - rep (9 * e) : ℕ) : ℤ) =
      ((H : ℤ) - S1) + (3 ^ e : ℕ) * (S1 + (3 ^ e : ℕ) * (Q + (3 ^ e : ℕ) * ((Q + Z) +
        (3 ^ e : ℕ) * (((L : ℤ) - (2 * Q + S1)) + (3 ^ e : ℕ) * (((2 * Q + S1 : ℕ) : ℤ) +
          (3 ^ e : ℕ) * (((T.cc * H : ℕ) : ℤ) - E + (3 ^ e : ℕ) * ((E : ℤ) +
            (3 ^ e : ℕ) * (T.N Q S1 Tc + T.jg * Z)))))))) := by
  have h6 := hS.E6
  have hPZ : (2 * ((r - rep (9 * e) : ℕ) : ℤ) + (q : ℤ) ^ 9 : ℤ) = 2 * r + 1 := by
    have hcast : ((2 * (r - rep (9 * e)) + q ^ 9 : ℕ) : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by
      rw [hP2]
    push_cast at hcast
    exact hcast
  rw [hq] at h6 hPZ
  push_cast at h6 hPZ ⊢
  have h2 : (2 : ℤ) * ((r - rep (9 * e) : ℕ) : ℤ) =
      2 * (((H : ℤ) - S1) + (3 : ℤ) ^ e * (S1 + (3 : ℤ) ^ e * (Q + (3 : ℤ) ^ e * ((Q + Z) +
        (3 : ℤ) ^ e * (((L : ℤ) - (2 * Q + S1)) + (3 : ℤ) ^ e * ((2 * (Q : ℤ) + S1) +
          (3 : ℤ) ^ e * (((T.cc : ℤ) * H) - E + (3 : ℤ) ^ e * ((E : ℤ) +
            (3 : ℤ) ^ e * (T.N Q S1 Tc + T.jg * Z))))))))) := by
    linear_combination hPZ + h6
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

/-- The nine fields are the successive base-`q` chunks of the Boolean packed word. -/
theorem fields91 (hU : 3 * T.Uthird + T.ε < 3 * T.B) (hI : Input91 T Ninit Linit) :
    ∃ e, q = 3 ^ e ∧ Fields91 T Q S1 Tc E H L Z e := by
  obtain ⟨e, -, hq, -, -, -, hrep, hP2, -, hPb⟩ := mask91 hT hP hS
  refine ⟨e, hq, ?_⟩
  have hPb' : Bool3 (r - rep (9 * e)) := hPb
  have hGNle := GN_le_rep91 hT hP hS hq hrep hP2 hPb'
  have hGNpos := GN_pos91 hT hP hS
  have hHq := H_bound91 hT hP hS
  have hM1q := M1_small91 hT hP hS
  have hLq := L_small91 hT hP hS
  have hZq := Z_small91 hT hP hS
  have hccq := ccH_small91 hT hP hS
  have hEq := E_small91 hT hP hS hU hI hq hGNle
  have hrepe : 2 * rep e + 1 = 3 ^ e := two_mul_rep_add_one e
  have hqZ : ((3 ^ e : ℕ) : ℤ) = (q : ℤ) := by rw [hq]
  have hHZ : 2 * (H : ℤ) + 1 ≤ q := by exact_mod_cast hHq
  have hM1Z : 162 * (2 * (Q : ℤ) + S1) ≤ q := by exact_mod_cast hM1q
  have hLZ : 80 * (L : ℤ) < q := by exact_mod_cast hLq
  have hZZ : 729 * (Z : ℤ) < 2 * q := by exact_mod_cast hZq
  have hccZ : 243 * ((T.cc : ℤ) * H) < q := by exact_mod_cast hccq
  have hEZ : 2 * (E : ℤ) < q := by exact_mod_cast hEq
  have hrepZ : 2 * (rep e : ℤ) + 1 = q := by rw [hq]; exact_mod_cast hrepe
  have hQ0 : (0 : ℤ) ≤ Q := by positivity
  have hS10 : (0 : ℤ) ≤ S1 := by positivity
  have hZ0 : (0 : ℤ) ≤ Z := by positivity
  have hL0 : (0 : ℤ) ≤ L := by positivity
  have hE0 : (0 : ℤ) ≤ E := by positivity
  have hH0 : (0 : ℤ) ≤ H := by positivity
  have hcc0 : (0 : ℤ) ≤ (T.cc : ℤ) * H := by positivity
  have hq0 : (0 : ℤ) < q := by have := hP.q; exact_mod_cast this
  have hpack := packed_eq91 hP hS hq hP2
  set P0 := r - rep (9 * e) with hP0
  -- step 0: `S₀ = H − S₁`
  obtain ⟨h0, h0'⟩ := chunk_step hPb' hpack (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P1 := P0 / 3 ^ e with hP1
  have hb1 : Bool3 P1 := hPb'.div_pow e
  -- step 1: `S₁`
  obtain ⟨h1, h1'⟩ := chunk_step hb1 h0'.symm (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P2 := P1 / 3 ^ e with hP2d
  have hb2 : Bool3 P2 := hb1.div_pow e
  -- step 2: `Q`
  obtain ⟨h2, h2'⟩ := chunk_step hb2 h1'.symm (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P3 := P2 / 3 ^ e with hP3
  have hb3 : Bool3 P3 := hb2.div_pow e
  -- step 3: `G = Q + Z`
  obtain ⟨h3, h3'⟩ := chunk_step hb3 h2'.symm (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P4 := P3 / 3 ^ e with hP4
  have hb4 : Bool3 P4 := hb3.div_pow e
  -- step 4: `M₀ = L − M₁`
  obtain ⟨h4, h4'⟩ := chunk_step hb4 h3'.symm (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P5 := P4 / 3 ^ e with hP5
  have hb5 : Bool3 P5 := hb4.div_pow e
  -- step 5: `M₁`
  obtain ⟨h5, h5'⟩ := chunk_step hb5 h4'.symm (by rw [hqZ]; push_cast; linarith)
    (by rw [hqZ]; push_cast; linarith)
  set P6 := P5 / 3 ^ e with hP6
  have hb6 : Bool3 P6 := hb5.div_pow e
  -- step 6: `Ē = cc·H − E`
  obtain ⟨h6, h6'⟩ := chunk_step hb6 h5'.symm (by rw [hqZ]; push_cast; linarith)
    (by rw [hqZ]; push_cast; linarith)
  set P7 := P6 / 3 ^ e with hP7
  have hb7 : Bool3 P7 := hb6.div_pow e
  -- step 7: `E`
  obtain ⟨h7, h7'⟩ := chunk_step hb7 h6'.symm (by rw [hqZ]; linarith) (by rw [hqZ]; linarith)
  set P8 := P7 / 3 ^ e with hP8
  have hb8 : Bool3 P8 := hb7.div_pow e
  -- the nonnegativity of the complements
  have hS1H : S1 ≤ H := by
    have : (0 : ℤ) ≤ ((P0 % 3 ^ e : ℕ) : ℤ) := by positivity
    have : (S1 : ℤ) ≤ H := by linarith
    exact_mod_cast this
  have hM1L : 2 * Q + S1 ≤ L := by
    have : (0 : ℤ) ≤ ((P4 % 3 ^ e : ℕ) : ℤ) := by positivity
    have : (2 * (Q : ℤ) + S1) ≤ L := by linarith
    exact_mod_cast this
  have hEcc : E ≤ T.cc * H := by
    have : (0 : ℤ) ≤ ((P6 % 3 ^ e : ℕ) : ℤ) := by positivity
    have : (E : ℤ) ≤ ((T.cc * H : ℕ) : ℤ) := by linarith
    exact_mod_cast this
  -- the fields as natural numbers
  have eS0 : H - S1 = P0 % 3 ^ e := by
    have : ((H - S1 : ℕ) : ℤ) = ((P0 % 3 ^ e : ℕ) : ℤ) := by rw [Nat.cast_sub hS1H]; exact h0
    exact_mod_cast this
  have eS1 : S1 = P1 % 3 ^ e := by exact_mod_cast h1
  have eQ : Q = P2 % 3 ^ e := by exact_mod_cast h2
  have eG : Q + Z = P3 % 3 ^ e := by exact_mod_cast h3
  have eM0 : L - (2 * Q + S1) = P4 % 3 ^ e := by
    have : ((L - (2 * Q + S1) : ℕ) : ℤ) = ((P4 % 3 ^ e : ℕ) : ℤ) := by
      rw [Nat.cast_sub hM1L]; push_cast; exact h4
    exact_mod_cast this
  have eM1 : 2 * Q + S1 = P5 % 3 ^ e := by exact_mod_cast h5
  have eEbar : T.cc * H - E = P6 % 3 ^ e := by
    have : ((T.cc * H - E : ℕ) : ℤ) = ((P6 % 3 ^ e : ℕ) : ℤ) := by
      rw [Nat.cast_sub hEcc]; exact h6
    exact_mod_cast this
  have eE : E = P7 % 3 ^ e := by exact_mod_cast h7
  refine ⟨hS1H, hM1L, hEcc, hGNpos, hGNle, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eS0]; exact hPb'.mod_pow e
  · rw [eS1]; exact hb1.mod_pow e
  · rw [eQ]; exact hb2.mod_pow e
  · rw [eG]; exact hb3.mod_pow e
  · rw [eM0]; exact hb4.mod_pow e
  · rw [eM1]; exact hb5.mod_pow e
  · rw [eEbar]; exact hb6.mod_pow e
  · rw [eE]; exact hb7.mod_pow e
  · intro GN hGN
    have : (GN : ℤ) = (P8 : ℤ) := by rw [hGN]; exact h7'
    have : GN = P8 := by exact_mod_cast this
    rw [this]; exact hb8
  · rw [← hq]; exact hHq
  · rw [← hq]; exact hLq
  · rw [← hq]; exact hZq
  · rw [← hq]; exact hccq
  · rw [← hq]; exact hM1q
  · rw [← hq]; exact hEq

end Fields

end Jones1980
