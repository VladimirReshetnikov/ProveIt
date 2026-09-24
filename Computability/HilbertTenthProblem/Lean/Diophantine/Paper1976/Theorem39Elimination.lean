import Diophantine.Paper1976.Theorem39d

/-!
# The ten-witness form of the 1976 prime criterion

The fourteen capital letters in Theorem 3.9 are integer polynomials in the
parameter and the ten remaining natural witnesses.  The rational inequality
is replaced by a positive polynomial margin; its strictness also enforces
the nonzero denominator.  Relation combining and degree estimates are separate
steps, not assertions of this file.
-/

namespace JSWW1976

/-- The capital letters eliminated after Theorem 3.9. -/
structure Elim39Values where
  M : ℤ
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
  E : ℤ
  F : ℤ
  G : ℤ
  H : ℤ
  I : ℤ
  K : ℤ
  L : ℤ
  R : ℤ
  S : ℤ

/-- All subtractions here are integer subtraction. -/
def elim39Values (k n x w m i j p l r z : ℤ) : Elim39Values :=
  let M := 16 * n * x * (w + 2) + 1
  let A := M * (x + 1)
  let B := n + 1
  let C := m + B
  let D := (A ^ 2 - 1) * C ^ 2 + 1
  let E := 2 * (i + 1) * D * C ^ 2
  let F := (A ^ 2 - 1) * E ^ 2 + 1
  let G := A + F * (F - A)
  let H := B + 2 * (j + 1) * C
  let I := (G ^ 2 - 1) * H ^ 2 + 1
  let K := n + 1 + p * (M - 1) - k
  let L := k + 1 + l * (M * x - 1)
  let R := k + 1 + r * (M * n * x - 1)
  let S := (z + 1) * (k + 1) - 2
  ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S⟩

private structure Elim39Equations (k n x w m i j p l r z : ℤ) (v : Elim39Values) : Prop where
  M : v.M = 16 * n * x * (w + 2) + 1
  A : v.A = v.M * (x + 1)
  B : v.B = n + 1
  C : v.C = m + v.B
  D : v.D = (v.A ^ 2 - 1) * v.C ^ 2 + 1
  E : v.E = 2 * (i + 1) * v.D * v.C ^ 2
  F : v.F = (v.A ^ 2 - 1) * v.E ^ 2 + 1
  G : v.G = v.A + v.F * (v.F - v.A)
  H : v.H = v.B + 2 * (j + 1) * v.C
  I : v.I = (v.G ^ 2 - 1) * v.H ^ 2 + 1
  K : v.K = n + 1 + p * (v.M - 1) - k
  L : v.L = k + 1 + l * (v.M * x - 1)
  R : v.R = k + 1 + r * (v.M * n * x - 1)
  S : v.S = (z + 1) * (k + 1) - 2

private theorem elim39Values_spec (k n x w m i j p l r z : ℤ) :
    Elim39Equations k n x w m i j p l r z (elim39Values k n x w m i j p l r z) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem Elim39Equations.unique {k n x w m i j p l r z : ℤ}
    {v : Elim39Values} (h : Elim39Equations k n x w m i j p l r z v) :
    v = elim39Values k n x w m i j p l r z := by
  rcases v with ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S⟩
  rcases h with ⟨hM, hA, hB, hC, hD, hE, hF, hG, hH, hI, hK, hL, hR, hS⟩
  dsimp only at hM hA hB hC hD hE hF hG hH hI hK hL hR hS
  subst M A B C D E F G H I K L R S
  rfl

/-- The denominator after cancelling the factors `K L` and `C²`. -/
def elim39Denominator (C K L R w x : ℤ) : ℤ :=
  (C - (w + 1) * x * K * L) * (C - R) ^ 2

/-- The matching numerator. -/
def elim39Numerator (C K R : ℤ) : ℤ := R * K * C ^ 2

/-- The strict polynomial margin replacing condition (XIV). -/
def elim39Margin (C K L R S w x : ℤ) : ℤ :=
  let d := elim39Denominator C K L R w x
  d ^ 2 - 4 * (elim39Numerator C K R - (S + 1) * d) ^ 2

/-- Clearing (XIV) preserves the definedness requirement. -/
theorem beta_defined_iff_margin {C K L R S w x : ℕ}
    (hC : 0 < C) (hK : 0 < K) (hL : 0 < L) :
    ((σ C K L - (w + 1) * x ≠ 0 ∧ R ≠ C) ∧
      (β C K L R w x - (S + 1)) ^ 2 < 1 / 4) ↔
    0 < elim39Margin C K L R S w x := by
  let d : ℤ := elim39Denominator C K L R w x
  let a : ℤ := elim39Numerator C K R
  have hC0 : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hd : (d : ℝ) =
      ((C : ℝ) - (w + 1) * x * K * L) * ((C : ℝ) - R) ^ 2 := by
    simp [d, elim39Denominator]
  have ha : (a : ℝ) = (R : ℝ) * K * C ^ 2 := by
    simp [a, elim39Numerator]
  have hs_eq : (σ C K L - (w + 1) * x) * ((K : ℝ) * L) =
      (C : ℝ) - (w + 1) * x * K * L := by
    unfold σ
    field_simp
  have hdefined : (d : ℝ) ≠ 0 ↔ σ C K L - (w + 1) * x ≠ 0 ∧ R ≠ C := by
    rw [hd, ← hs_eq, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : 2 ≠ 0)]
    simp only [sub_ne_zero]
    constructor
    · rintro ⟨⟨hs, _⟩, hRC⟩
      exact ⟨hs, fun h => hRC (by exact_mod_cast h.symm)⟩
    · rintro ⟨hs, hRC⟩
      exact ⟨⟨hs, mul_ne_zero hK0 hL0⟩, fun h => hRC (by exact_mod_cast h.symm)⟩
  have hbeta (hd0 : (d : ℝ) ≠ 0) : β C K L R w x * (d : ℝ) = a := by
    obtain ⟨hs, hRC⟩ := hdefined.mp hd0
    have hRC0 : (C : ℝ) - R ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm hRC)
    have hsmall : 1 - (R : ℝ) / C ≠ 0 := by
      intro h
      apply hRC0
      field_simp at h
      linarith
    rw [hd, ha, ← hs_eq]
    unfold β
    field_simp
  have hcast : (0 < elim39Margin C K L R S w x) ↔
      0 < (d : ℝ) ^ 2 - 4 * ((a : ℝ) - ((S : ℝ) + 1) * d) ^ 2 := by
    unfold elim39Margin
    change (0 < d ^ 2 - 4 * (a - ((S : ℤ) + 1) * d) ^ 2) ↔ _
    exact_mod_cast (Iff.rfl :
      (0 < d ^ 2 - 4 * (a - ((S : ℤ) + 1) * d) ^ 2) ↔
      (0 < d ^ 2 - 4 * (a - ((S : ℤ) + 1) * d) ^ 2))
  rw [hcast]
  constructor
  · rintro ⟨hdef, hlt⟩
    have hd0 := hdefined.mpr hdef
    have hb := hbeta hd0
    have hdpos : 0 < (d : ℝ) ^ 2 := sq_pos_of_ne_zero hd0
    have he : ((a : ℝ) - ((S : ℝ) + 1) * d) ^ 2 =
        (β C K L R w x - (S + 1)) ^ 2 * (d : ℝ) ^ 2 := by
      rw [← hb]
      ring
    rw [he]
    nlinarith [mul_lt_mul_of_pos_right hlt hdpos]
  · intro hlt
    have hd0 : (d : ℝ) ≠ 0 := by
      intro he
      rw [he] at hlt
      nlinarith [sq_nonneg ((a : ℝ) - ((S : ℝ) + 1) * 0)]
    refine ⟨hdefined.mp hd0, ?_⟩
    have hb := hbeta hd0
    have he : ((a : ℝ) - ((S : ℝ) + 1) * d) ^ 2 =
        (β C K L R w x - (S + 1)) ^ 2 * (d : ℝ) ^ 2 := by
      rw [← hb]
      ring
    rw [he] at hlt
    have hdpos : 0 < (d : ℝ) ^ 2 := sq_pos_of_ne_zero hd0
    have hmul : (4 * (β C K L R w x - (S + 1)) ^ 2) * (d : ℝ) ^ 2 <
        1 * (d : ℝ) ^ 2 := by nlinarith only [hlt]
    have hsmall := (mul_lt_mul_iff_left₀ hdpos).mp hmul
    linarith

/-- Definition 3.7, now as an integer polynomial. -/
def elim39U (x y : ℤ) : ℤ := (x + 2) ^ 3 * (x + 4) * (y + 1) ^ 2 + 1

@[simp] theorem elim39U_natCast (x y : ℕ) : elim39U x y = (U x y : ℤ) := by
  simp [elim39U, U]

/-- The six square tests, in the order (I), (II), (VII), (XV), (XVI), (XVII). -/
def elim39Squares (k n x w m i j p l r z : ℤ) : Fin 6 → ℤ :=
  let v := elim39Values k n x w m i j p l r z
  ![elim39U (2 * k) n, elim39U (2 * n) x, v.D * v.F * v.I,
    (v.M ^ 2 - 1) * v.K ^ 2 + 1,
    ((v.M * x) ^ 2 - 1) * v.L ^ 2 + 1,
    ((v.M * n * x) ^ 2 - 1) * v.R ^ 2 + 1]

/-- Exactly ten natural witnesses remain. The capital letters are abbreviations. -/
structure ReducedSys39 (k n x w m i j p l r z : ℕ) : Prop where
  squares : ∀ a : Fin 6, IsSquare (elim39Squares k n x w m i j p l r z a)
  dvd : let v := elim39Values k n x w m i j p l r z; v.F ∣ v.H - v.C
  margin : let v := elim39Values k n x w m i j p l r z;
    0 < elim39Margin v.C v.K v.L v.R v.S w x

/-- The four square tests retained after the two growth conditions. -/
def elim39GrowthSquares (k n x w m i j p l r z : ℤ) : Fin 4 → ℤ :=
  let v := elim39Values k n x w m i j p l r z
  ![v.D * v.F * v.I, (v.M ^ 2 - 1) * v.K ^ 2 + 1,
    ((v.M * x) ^ 2 - 1) * v.L ^ 2 + 1,
    ((v.M * n * x) ^ 2 - 1) * v.R ^ 2 + 1]

/-- The capital-free system needs only the two growth inequalities. -/
structure ReducedGrowthSys39 (k n x w m i j p l r z : ℕ) : Prop where
  growthN : (2 * k) ^ (2 * k) < n
  growthX : (2 * n) ^ (2 * n) < x
  squares : ∀ a : Fin 4, IsSquare (elim39GrowthSquares k n x w m i j p l r z a)
  dvd : let v := elim39Values k n x w m i j p l r z; v.F ∣ v.H - v.C
  margin : let v := elim39Values k n x w m i j p l r z;
    0 < elim39Margin v.C v.K v.L v.R v.S w x

private structure Elim39Bounds (v : Elim39Values) : Prop where
  M : 1 < v.M
  A : 1 < v.A
  B : 0 < v.B
  C : 0 < v.C
  D : 0 < v.D
  E : 0 < v.E
  F : 0 < v.F
  G : 1 < v.G
  H : 0 < v.H
  I : 0 < v.I
  K : 0 < v.K
  L : 0 < v.L
  R : 0 < v.R
  S : 0 ≤ v.S

private theorem elim39Values_bounds {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (hx : 0 < x) :
    Elim39Bounds (elim39Values k n x w m i j p l r z) := by
  let v := elim39Values k n x w m i j p l r z
  have e := elim39Values_spec k n x w m i j p l r z
  change Elim39Equations _ _ _ _ _ _ _ _ _ _ _ v at e
  have hkZ : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hknZ : (k : ℤ) < n := by exact_mod_cast hkn
  have hxZ : (0 : ℤ) < x := by exact_mod_cast hx
  have hnZ : (0 : ℤ) < n := by omega
  have hM : 1 < v.M := by
    rw [e.M]
    have : 0 < 16 * (n : ℤ) * x * (w + 2) := by positivity
    omega
  have hA : 1 < v.A := by rw [e.A]; nlinarith
  have hB : 0 < v.B := by rw [e.B]; omega
  have hC : 0 < v.C := by rw [e.C]; omega
  have hA2 : 0 < v.A ^ 2 - 1 := by nlinarith
  have hD : v.A < v.D := by
    have hC2 : 1 ≤ v.C ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hC2 hA2.le
    rw [e.D]
    nlinarith
  have hD0 : 0 < v.D := by omega
  have hE : 0 < v.E := by rw [e.E]; positivity
  have hF : v.A < v.F := by
    have hE2 : 1 ≤ v.E ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hE2 hA2.le
    rw [e.F]
    nlinarith
  have hG : 1 < v.G := by
    have : 0 ≤ v.F * (v.F - v.A) := mul_nonneg (by omega) (by omega)
    rw [e.G]
    omega
  have hH : 0 < v.H := by rw [e.H]; positivity
  have hI : 0 < v.I := by
    have : 0 ≤ (v.G ^ 2 - 1) * v.H ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
    rw [e.I]
    omega
  have hK : 0 < v.K := by
    have : 0 ≤ (p : ℤ) * (v.M - 1) := mul_nonneg (by positivity) (by omega)
    rw [e.K]
    omega
  have hMx : 1 ≤ v.M * x := by nlinarith
  have hMnx : 1 ≤ v.M * n * x := by
    have : 1 ≤ v.M * n := by nlinarith
    nlinarith
  have hL : 0 < v.L := by
    have : 0 ≤ (l : ℤ) * (v.M * x - 1) := mul_nonneg (by positivity) (by omega)
    rw [e.L]
    omega
  have hR : 0 < v.R := by
    have : 0 ≤ (r : ℤ) * (v.M * n * x - 1) := mul_nonneg (by positivity) (by omega)
    rw [e.R]
    omega
  have hS : 0 ≤ v.S := by rw [e.S]; nlinarith [show (0 : ℤ) ≤ z by positivity]
  have hF0 : 0 < v.F := by omega
  exact ⟨hM, hA, hB, hC, hD0, hE, hF0, hG, hH, hI, hK, hL, hR, hS⟩

private theorem ReducedSys39.initial {k n x w m i j p l r z : ℕ}
    (h : ReducedSys39 k n x w m i j p l r z) :
    IsSquare (U (2 * k) n) ∧ IsSquare (U (2 * n) x) := by
  have h0 := h.squares 0
  have h1 := h.squares 1
  change IsSquare (elim39U (2 * (k : ℤ)) n) at h0
  change IsSquare (elim39U (2 * (n : ℤ)) x) at h1
  have e0 : elim39U (2 * (k : ℤ)) n = (U (2 * k) n : ℤ) := by simp [elim39U, U]
  have e1 : elim39U (2 * (n : ℤ)) x = (U (2 * n) x : ℤ) := by simp [elim39U, U]
  rw [e0, Int.isSquare_natCast_iff] at h0
  rw [e1, Int.isSquare_natCast_iff] at h1
  exact ⟨h0, h1⟩

private theorem GrowthSys39.cast_equations {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (hk : 1 ≤ k) (h : GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    Elim39Equations k n x w m i j p l r z
      ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S⟩ := by
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ :=
    basic_bounds hk h.cI h.cII
  have hM : 1 ≤ M := by rw [h.cIII]; omega
  have hMpos : 0 < M := by omega
  have hnpos : 0 < n := by omega
  have hxpos : 0 < x := by omega
  have hMx : 1 ≤ M * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMnx : 1 ≤ M * n * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · exact_mod_cast h.cIII
  · exact_mod_cast h.cIV
  · exact_mod_cast h.cV
  · exact_mod_cast h.cVI
  · have e := h.cVIII
    zify at e
    linear_combination e
  · exact_mod_cast h.cIX
  · have e := h.cX
    zify at e
    linear_combination e
  · have e := h.cXI
    zify at e
    linear_combination e
  · exact_mod_cast h.cXII
  · have e := h.cXIII
    zify at e
    linear_combination e
  · have e := h.cXVIII
    zify [hM] at e
    linear_combination e
  · have e := h.cXIX
    zify [hMx] at e
    exact e
  · have e := h.cXX
    zify [hMnx] at e
    exact e
  · have e := h.cXXI
    zify at e
    linear_combination e

/-- Eliminating the capital letters from a solution adds no witnesses. -/
theorem GrowthSys39.reduced {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (hk : 1 ≤ k) (h : GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    ReducedGrowthSys39 k n x w m i j p l r z := by
  have hv := (h.cast_equations hk).unique.symm
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ :=
    basic_bounds hk h.cI h.cII
  have hM : 1 ≤ M := by rw [h.cIII]; omega
  have hMpos : 0 < M := by omega
  have hnpos : 0 < n := by omega
  have hxpos : 0 < x := by omega
  have hMx : 1 ≤ M * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMnx : 1 ≤ M * n * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM2 : 1 ≤ M * M := Nat.mul_le_mul hM hM
  have hMx2 : 1 ≤ M * x * (M * x) := Nat.mul_le_mul hMx hMx
  have hMnx2 : 1 ≤ M * n * x * (M * n * x) := Nat.mul_le_mul hMnx hMnx
  refine ⟨h.cI, h.cII, ?_, ?_, ?_⟩
  · intro a
    fin_cases a
    · change IsSquare ((elim39Values k n x w m i j p l r z).D *
        (elim39Values k n x w m i j p l r z).F * (elim39Values k n x w m i j p l r z).I)
      rw [hv]
      change IsSquare ((D : ℤ) * F * I)
      exact_mod_cast h.cVII.1
    · change IsSquare (((elim39Values k n x w m i j p l r z).M ^ 2 - 1) *
        (elim39Values k n x w m i j p l r z).K ^ 2 + 1)
      rw [hv]
      have hs := Int.isSquare_natCast_iff.mpr h.cXV
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hM2,
        Nat.cast_one, pow_two] using hs
    · change IsSquare ((((elim39Values k n x w m i j p l r z).M * x) ^ 2 - 1) *
        (elim39Values k n x w m i j p l r z).L ^ 2 + 1)
      rw [hv]
      have hs := Int.isSquare_natCast_iff.mpr h.cXVI
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hMx2,
        Nat.cast_one, pow_two] using hs
    · change IsSquare ((((elim39Values k n x w m i j p l r z).M * n * x) ^ 2 - 1) *
        (elim39Values k n x w m i j p l r z).R ^ 2 + 1)
      rw [hv]
      have hs := Int.isSquare_natCast_iff.mpr h.cXVII
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hMnx2,
        Nat.cast_one, pow_two] using hs
  · change (elim39Values k n x w m i j p l r z).F ∣
      (elim39Values k n x w m i j p l r z).H - (elim39Values k n x w m i j p l r z).C
    rw [hv]
    exact h.cVII.2
  · change 0 < elim39Margin (elim39Values k n x w m i j p l r z).C
      (elim39Values k n x w m i j p l r z).K (elim39Values k n x w m i j p l r z).L
      (elim39Values k n x w m i j p l r z).R (elim39Values k n x w m i j p l r z).S w x
    rw [hv]
    exact (beta_defined_iff_margin (Nat.pos_of_ne_zero h.cXIV_def.2.2.1)
      (Nat.pos_of_ne_zero h.cXIV_def.1) (Nat.pos_of_ne_zero h.cXIV_def.2.1)).mp
      ⟨⟨h.cXIV_def.2.2.2.1, h.cXIV_def.2.2.2.2⟩, h.cXIV⟩

/-- A reduced solution reconstructs natural capital letters. -/
theorem ReducedGrowthSys39.exists_growthSys39 {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (h : ReducedGrowthSys39 k n x w m i j p l r z) :
    ∃ M A B C D E F G H I K L R S : ℕ,
      GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ := basic_bounds hk h.growthN h.growthX
  let v := elim39Values k n x w m i j p l r z
  have hb : Elim39Bounds v := elim39Values_bounds hk hkn (by omega)
  have e := elim39Values_spec k n x w m i j p l r z
  change Elim39Equations _ _ _ _ _ _ _ _ _ _ _ v at e
  let M := v.M.toNat
  have hMcast : (M : ℤ) = v.M := Int.toNat_of_nonneg (by have := hb.M; omega)
  let A := v.A.toNat
  have hAcast : (A : ℤ) = v.A := Int.toNat_of_nonneg (by have := hb.A; omega)
  let B := v.B.toNat
  have hBcast : (B : ℤ) = v.B := Int.toNat_of_nonneg hb.B.le
  let C := v.C.toNat
  have hCcast : (C : ℤ) = v.C := Int.toNat_of_nonneg hb.C.le
  let D := v.D.toNat
  have hDcast : (D : ℤ) = v.D := Int.toNat_of_nonneg hb.D.le
  let E := v.E.toNat
  have hEcast : (E : ℤ) = v.E := Int.toNat_of_nonneg hb.E.le
  let F := v.F.toNat
  have hFcast : (F : ℤ) = v.F := Int.toNat_of_nonneg hb.F.le
  let G := v.G.toNat
  have hGcast : (G : ℤ) = v.G := Int.toNat_of_nonneg (by have := hb.G; omega)
  let H := v.H.toNat
  have hHcast : (H : ℤ) = v.H := Int.toNat_of_nonneg hb.H.le
  let I := v.I.toNat
  have hIcast : (I : ℤ) = v.I := Int.toNat_of_nonneg hb.I.le
  let K := v.K.toNat
  have hKcast : (K : ℤ) = v.K := Int.toNat_of_nonneg hb.K.le
  let L := v.L.toNat
  have hLcast : (L : ℤ) = v.L := Int.toNat_of_nonneg hb.L.le
  let R := v.R.toNat
  have hRcast : (R : ℤ) = v.R := Int.toNat_of_nonneg hb.R.le
  let S := v.S.toNat
  have hScast : (S : ℤ) = v.S := Int.toNat_of_nonneg hb.S
  have eZ : Elim39Equations k n x w m i j p l r z
      ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S⟩ := by
    simpa only [hMcast, hAcast, hBcast, hCcast, hDcast, hEcast, hFcast, hGcast, hHcast, hIcast, hKcast, hLcast, hRcast, hScast] using e
  have hM : 1 ≤ M := by
    have hh := hb.M
    rw [← hMcast] at hh
    exact_mod_cast (show (1 : ℤ) ≤ M by omega)
  have hMpos : 0 < M := by omega
  have hnpos : 0 < n := by omega
  have hxpos : 0 < x := by omega
  have hMx : 1 ≤ M * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMnx : 1 ≤ M * n * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hM2 : 1 ≤ M * M := Nat.mul_le_mul hM hM
  have hMx2 : 1 ≤ M * x * (M * x) := Nat.mul_le_mul hMx hMx
  have hMnx2 : 1 ≤ M * n * x * (M * n * x) := Nat.mul_le_mul hMnx hMnx
  have hCpos : 0 < C := by
    have hh := hb.C
    rw [← hCcast] at hh
    exact_mod_cast hh
  have hKpos : 0 < K := by
    have hh := hb.K
    rw [← hKcast] at hh
    exact_mod_cast hh
  have hLpos : 0 < L := by
    have hh := hb.L
    rw [← hLcast] at hh
    exact_mod_cast hh
  have hmargin := h.margin
  change 0 < elim39Margin v.C v.K v.L v.R v.S w x at hmargin
  rw [← hCcast, ← hKcast, ← hLcast, ← hRcast, ← hScast] at hmargin
  obtain ⟨⟨hs, hRC⟩, hbeta⟩ := (beta_defined_iff_margin hCpos hKpos hLpos).mpr hmargin
  refine ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S,
    h.growthN, h.growthX, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨hKpos.ne', hLpos.ne', hCpos.ne', hs, hRC⟩, hbeta, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · zify
    exact eZ.M
  · zify
    exact eZ.A
  · zify
    exact eZ.B
  · zify
    exact eZ.C
  · constructor
    · have hs := h.squares 0
      change IsSquare (v.D * v.F * v.I) at hs
      rw [← hDcast, ← hFcast, ← hIcast] at hs
      exact_mod_cast hs
    · have hd := h.dvd
      change v.F ∣ v.H - v.C at hd
      rwa [← hFcast, ← hHcast, ← hCcast] at hd
  · zify
    linear_combination eZ.D
  · zify
    exact eZ.E
  · zify
    linear_combination eZ.F
  · zify
    linear_combination eZ.G
  · zify
    exact eZ.H
  · zify
    linear_combination eZ.I
  · have hs := h.squares 1
    change IsSquare ((v.M ^ 2 - 1) * v.K ^ 2 + 1) at hs
    rw [← hMcast, ← hKcast] at hs
    apply Int.isSquare_natCast_iff.mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hM2,
      Nat.cast_one, pow_two] using hs
  · have hs := h.squares 2
    change IsSquare (((v.M * x) ^ 2 - 1) * v.L ^ 2 + 1) at hs
    rw [← hMcast, ← hLcast] at hs
    apply Int.isSquare_natCast_iff.mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hMx2,
      Nat.cast_one, pow_two] using hs
  · have hs := h.squares 3
    change IsSquare (((v.M * n * x) ^ 2 - 1) * v.R ^ 2 + 1) at hs
    rw [← hMcast, ← hRcast] at hs
    apply Int.isSquare_natCast_iff.mp
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hMnx2,
      Nat.cast_one, pow_two] using hs
  · zify [hM]
    linear_combination eZ.K
  · zify [hMx]
    exact eZ.L
  · zify [hMnx]
    exact eZ.R
  · zify
    linear_combination eZ.S

/-- The divisor and dividend supplied to relation combining are positive for
every natural assignment, independently of the square tests. -/
theorem elim39Values_divisibility_positive (k n x w m i j p l r z : ℕ) :
    let v := elim39Values k n x w m i j p l r z
    0 < v.F ∧ 0 < v.H - v.C := by
  let v := elim39Values k n x w m i j p l r z
  have e := elim39Values_spec k n x w m i j p l r z
  change Elim39Equations _ _ _ _ _ _ _ _ _ _ _ v at e
  have hM : 1 ≤ v.M := by
    rw [e.M]
    have : 0 ≤ 16 * (n : ℤ) * x * (w + 2) := by positivity
    omega
  have hA : 1 ≤ v.A := by
    rw [e.A]
    have hx : (1 : ℤ) ≤ x + 1 := by omega
    nlinarith
  have hB : 0 < v.B := by rw [e.B]; omega
  have hC : 0 < v.C := by rw [e.C]; omega
  constructor
  · rw [e.F]
    have : 0 ≤ (v.A ^ 2 - 1) * v.E ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
    omega
  · have hj : (1 : ℤ) ≤ 2 * ((j : ℤ) + 1) := by omega
    have hm := mul_le_mul_of_nonneg_right hj hC.le
    rw [e.H]
    linarith

/-- The original two square conditions imply the weaker growth conditions. -/
theorem ReducedSys39.toReducedGrowthSys39 {k n x w m i j p l r z : ℕ}
    (h : ReducedSys39 k n x w m i j p l r z) :
    ReducedGrowthSys39 k n x w m i j p l r z := by
  obtain ⟨h0, h1⟩ := h.initial
  refine ⟨lt_of_U_square h0, lt_of_U_square h1, ?_, h.dvd, h.margin⟩
  intro a
  fin_cases a
  · exact h.squares 2
  · exact h.squares 3
  · exact h.squares 4
  · exact h.squares 5

/-- Restoring the two original squares recovers the original reduced system. -/
theorem ReducedGrowthSys39.toReducedSys39 {k n x w m i j p l r z : ℕ}
    (h : ReducedGrowthSys39 k n x w m i j p l r z)
    (h0 : IsSquare (U (2 * k) n)) (h1 : IsSquare (U (2 * n) x)) :
    ReducedSys39 k n x w m i j p l r z := by
  refine ⟨?_, h.dvd, h.margin⟩
  intro a
  fin_cases a
  · change IsSquare (elim39U (2 * (k : ℤ)) n)
    have he : elim39U (2 * (k : ℤ)) n = (U (2 * k) n : ℤ) := by simp [elim39U, U]
    rw [he, Int.isSquare_natCast_iff]
    exact h0
  · change IsSquare (elim39U (2 * (n : ℤ)) x)
    have he : elim39U (2 * (n : ℤ)) x = (U (2 * n) x : ℤ) := by simp [elim39U, U]
    rw [he, Int.isSquare_natCast_iff]
    exact h1
  · exact h.squares 0
  · exact h.squares 1
  · exact h.squares 2
  · exact h.squares 3

/-- Eliminating the capital letters from an original solution adds no witnesses. -/
theorem Sys39.reduced {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (hk : 1 ≤ k) (h : Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    ReducedSys39 k n x w m i j p l r z :=
  (h.toGrowthSys39.reduced hk).toReducedSys39 h.cI h.cII

/-- A reduced original solution reconstructs the same natural capital letters. -/
theorem ReducedSys39.exists_sys39 {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (h : ReducedSys39 k n x w m i j p l r z) :
    ∃ M A B C D E F G H I K L R S : ℕ,
      Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  obtain ⟨h0, h1⟩ := h.initial
  obtain ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS⟩ :=
    h.toReducedGrowthSys39.exists_growthSys39 hk
  exact ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS.toSys39 h0 h1⟩

/-- Exact elimination with the growth hypotheses exposed. -/
theorem reducedGrowthSys39_iff_exists_growthSys39 {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) :
    ReducedGrowthSys39 k n x w m i j p l r z ↔
      ∃ M A B C D E F G H I K L R S : ℕ,
        GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  constructor
  · exact ReducedGrowthSys39.exists_growthSys39 hk
  · rintro ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, h⟩
    exact h.reduced hk

/-- The reduced growth system already suffices for primality. -/
theorem ReducedGrowthSys39.prime {k n x w m i j p l r z : ℕ}
    (hk : 1 ≤ k) (h : ReducedGrowthSys39 k n x w m i j p l r z) : Nat.Prime (k + 1) := by
  obtain ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS⟩ := h.exists_growthSys39 hk
  exact theorem_3_9_sufficiency_of_growth hk hS

/-- The exact elimination equivalence, retaining all ten natural witnesses. -/
theorem reducedSys39_iff_exists_sys39 {k n x w m i j p l r z : ℕ} (hk : 1 ≤ k) :
    ReducedSys39 k n x w m i j p l r z ↔
      ∃ M A B C D E F G H I K L R S : ℕ,
        Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  constructor
  · exact ReducedSys39.exists_sys39 hk
  · rintro ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, h⟩
    exact h.reduced hk

/-- Theorem 3.9 with precisely ten natural witnesses and eight polynomial tests. -/
theorem theorem_3_9_reduced {k : ℕ} (hk : 1 ≤ k) :
    Nat.Prime (k + 1) ↔ ∃ n x w m i j p l r z : ℕ, ReducedSys39 k n x w m i j p l r z := by
  rw [theorem_3_9 hk]
  constructor
  · rintro ⟨n, x, w, m, i, j, p, l, r, z, M, A, B, C, D, E, F, G, H, I, K, L, R, S, h⟩
    exact ⟨n, x, w, m, i, j, p, l, r, z, h.reduced hk⟩
  · rintro ⟨n, x, w, m, i, j, p, l, r, z, h⟩
    obtain ⟨M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS⟩ := h.exists_sys39 hk
    exact ⟨n, x, w, m, i, j, p, l, r, z, M, A, B, C, D, E, F, G, H, I, K, L, R, S, hS⟩

end JSWW1976
